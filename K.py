#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
K.py – خزندهٔ وحشی هوشمند (Wild Crawler)
مستقل از Bot.py اما قابل فراخوانی توسط آن
"""

import os, sys, json, time, uuid, hashlib, zipfile, csv, io
import requests, threading, queue, traceback
from urllib.parse import urlparse, urljoin, unquote
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from bs4 import BeautifulSoup
from playwright.sync_api import sync_playwright
import re

# ═══════ پیکربندی ═══════
BOT_TOKEN = os.getenv("BALE_BOT_TOKEN", "").strip()
if not BOT_TOKEN:
    print("ERROR: BALE_BOT_TOKEN not set", file=sys.stderr)
    sys.exit(1)
BALE_API_URL = f"https://tapi.bale.ai/bot{BOT_TOKEN}"
REQUEST_TIMEOUT = 30

MAX_DEPTH = 3
MAX_PAGES = 200
MAX_TIME = 20 * 60          # ۲۰ دقیقه
MAX_TOTAL_SIZE = 500 * 1024 * 1024   # ۵۰۰ مگابایت
DOMAIN_DELAY = 1.0          # تأخیر بین درخواست‌ها به یک دامنه (ثانیه)

# ═══════ ابزارهای API ═══════
def send_message(chat_id, text, reply_markup=None):
    params = {"chat_id": chat_id, "text": text}
    if reply_markup:
        params["reply_markup"] = json.dumps(reply_markup)
    try:
        r = requests.post(f"{BALE_API_URL}/sendMessage", json=params, timeout=REQUEST_TIMEOUT)
        if r.status_code == 200 and r.json().get("ok"):
            return r.json()["result"]
    except:
        pass
    return None

def send_document(chat_id, file_path, caption=""):
    if not os.path.exists(file_path):
        return None
    try:
        with open(file_path, "rb") as f:
            r = requests.post(f"{BALE_API_URL}/sendDocument",
                              data={"chat_id": chat_id, "caption": caption},
                              files={"document": (os.path.basename(file_path), f)},
                              timeout=REQUEST_TIMEOUT * 2)
        if r.status_code == 200 and r.json().get("ok"):
            return r.json()["result"]
    except:
        pass
    return None

# ═══════ ابزارهای کمکی ═══════
def is_valid_url(url):
    return url and url.startswith(("http://", "https://"))

def get_domain(url):
    return urlparse(url).netloc.lower()

def is_same_domain(url1, url2):
    return get_domain(url1) == get_domain(url2)

def extract_links_from_html(html, base_url):
    soup = BeautifulSoup(html, "html.parser")
    links = set()
    for tag in soup.find_all(["a", "link", "script", "img", "iframe", "source", "video", "audio"]):
        for attr in ("href", "src", "data-url", "data-href", "data-link"):
            val = tag.get(attr)
            if val:
                try:
                    full = urljoin(base_url, val)
                    if is_valid_url(full):
                        links.add(full)
                except:
                    pass
    # thumbnailها و srcset
    for tag in soup.find_all("img"):
        srcset = tag.get("srcset") or ""
        for part in srcset.split(","):
            url_part = part.strip().split(" ")[0]
            if url_part:
                try:
                    full = urljoin(base_url, url_part)
                    if is_valid_url(full):
                        links.add(full)
                except:
                    pass
    # لینک‌های موجود در اسکریپت‌ها
    for script in soup.find_all("script"):
        if script.string:
            matches = re.findall(r'https?://[^\s"\'<>]+', script.string)
            for m in matches:
                links.add(m)
    return list(links)

def categorize_url(url, content_type=None):
    """نوع منبع را بر اساس URL و Content-Type تشخیص می‌دهد"""
    path = urlparse(url).path.lower()
    if content_type:
        ct = content_type.lower()
        if "image" in ct:
            return "image"
        if "video" in ct or "mpegurl" in ct or "dash+xml" in ct:
            return "video"
        if "application/pdf" in ct:
            return "pdf"
    if any(path.endswith(ext) for ext in ('.jpg','.jpeg','.png','.gif','.svg','.webp','.bmp','.ico')):
        return "image"
    if any(path.endswith(ext) for ext in ('.mp4','.mkv','.webm','.avi','.mov','.flv','.wmv')):
        return "video"
    if any(path.endswith(ext) for ext in ('.m3u8','.mpd')):
        return "video"
    if path.endswith('.pdf'):
        return "pdf"
    if any(path.endswith(ext) for ext in ('.zip','.rar','.7z','.tar','.gz','.exe','.apk','.dmg','.iso','.whl','.deb','.rpm')):
        return "archive"
    return "page"  # احتمالاً صفحه HTML

# ═══════ خزنده اصلی ═══════
class WildCrawler:
    def __init__(self, start_url, chat_id):
        self.start_url = start_url
        self.chat_id = chat_id
        self.visited = set()
        self.queue = queue.Queue()
        self.queue.put((start_url, 0))
        self.lock = threading.Lock()
        self.total_pages = 0
        self.total_files = 0
        self.total_errors = 0
        self.total_size = 0
        self.start_time = time.time()
        self.stop_flag = False
        self.domain_last_request = defaultdict(float)
        self.results_dir = f"crawl_results_{uuid.uuid4().hex[:8]}"
        os.makedirs(self.results_dir, exist_ok=True)
        # زیرشاخه‌ها
        for sub in ["images", "videos", "pdfs", "texts", "others"]:
            os.makedirs(os.path.join(self.results_dir, sub), exist_ok=True)
        self.csv_file = os.path.join(self.results_dir, "all_links.csv")
        self.csv_writer = None
        self._init_csv()

    def _init_csv(self):
        self.csv_file_handle = open(self.csv_file, "w", newline="", encoding="utf-8")
        self.csv_writer = csv.writer(self.csv_file_handle)
        self.csv_writer.writerow(["url", "status", "content_type", "type", "depth", "note"])

    def log_link(self, url, status, content_type="", typ="", depth=0, note=""):
        with self.lock:
            self.csv_writer.writerow([url, status, content_type, typ, depth, note])
            self.csv_file_handle.flush()

    def can_fetch_domain(self, domain):
        """رعایت تأخیر بین درخواست‌ها"""
        now = time.time()
        with self.lock:
            last = self.domain_last_request[domain]
            if now - last < DOMAIN_DELAY:
                time.sleep(DOMAIN_DELAY - (now - last))
            self.domain_last_request[domain] = time.time()

    def fetch_page(self, url):
        """دریافت HTML یا محتوای صفحه با requests"""
        headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}
        try:
            self.can_fetch_domain(get_domain(url))
            r = requests.get(url, timeout=30, headers=headers, stream=True)
            content_type = r.headers.get("Content-Type", "")
            # اگر محتوای غیر HTML بود
            if "text/html" not in content_type:
                return None, content_type, r.content
            # HTML
            # خواندن تا نهایتاً 5MB
            content = b""
            for chunk in r.iter_content(chunk_size=8192):
                content += chunk
                if len(content) > 5 * 1024 * 1024:
                    break
            return content.decode("utf-8", errors="ignore"), content_type, content
        except Exception as e:
            raise e

    def fetch_page_with_playwright(self, url):
        """برای صفحات جاوااسکریپتی"""
        try:
            self.can_fetch_domain(get_domain(url))
            pw = sync_playwright().start()
            browser = pw.chromium.launch(headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
            page = browser.new_page()
            page.goto(url, timeout=30000, wait_until="domcontentloaded")
            page.wait_for_timeout(1000)
            html = page.content()
            page.close()
            browser.close()
            pw.stop()
            return html, "text/html; charset=utf-8", None
        except Exception as e:
            raise e

    def download_file(self, url, category, name=None):
        """دانلود یک فایل و ذخیره در پوشه مناسب"""
        headers = {"User-Agent": "Mozilla/5.0"}
        try:
            self.can_fetch_domain(get_domain(url))
            r = requests.get(url, timeout=30, headers=headers, stream=True)
            r.raise_for_status()
            content_type = r.headers.get("Content-Type", "")
            ext = os.path.splitext(urlparse(url).path)[1]
            if not ext and category == "image":
                ext = ".jpg"
            elif not ext:
                ext = ".file"
            if not name:
                name = f"{uuid.uuid4().hex[:8]}{ext}"
            path = os.path.join(self.results_dir, category + "s", name)
            size = 0
            with open(path, "wb") as f:
                for chunk in r.iter_content(8192):
                    if self.stop_flag:
                        return None, 0
                    f.write(chunk)
                    size += len(chunk)
                    if size + self.total_size > MAX_TOTAL_SIZE:
                        # حذف فایل ناقص
                        os.remove(path)
                        return None, size
            with self.lock:
                self.total_size += size
            return path, size
        except Exception as e:
            raise e

    def process_page(self, url, depth):
        if self.stop_flag:
            return
        if depth > MAX_DEPTH:
            return
        with self.lock:
            if url in self.visited:
                return
            self.visited.add(url)
            self.total_pages += 1
            if self.total_pages > MAX_PAGES:
                self.stop_flag = True
                return
            if time.time() - self.start_time > MAX_TIME:
                self.stop_flag = True
                return

        self.log_link(url, "processing", "", "page", depth)
        try:
            html, ct, raw = self.fetch_page(url)
            if html:
                # استخراج لینک‌ها
                links = extract_links_from_html(html, url)
                for link in links:
                    if self.stop_flag: break
                    cat = categorize_url(link)
                    if cat in ("image", "video", "pdf", "archive"):
                        try:
                            fname = unquote(os.path.basename(urlparse(link).path))
                            path, size = self.download_file(link, cat, name=fname)
                            if path:
                                with self.lock:
                                    self.total_files += 1
                                self.log_link(link, "downloaded", ct or "", cat, depth, f"size={size}")
                            else:
                                self.log_link(link, "skipped (size limit?)", "", cat, depth)
                        except Exception as e:
                            with self.lock:
                                self.total_errors += 1
                            self.log_link(link, "error", "", cat, depth, str(e))
                    else:
                        # page
                        if depth < MAX_DEPTH and is_same_domain(link, url):
                            self.queue.put((link, depth+1))
                # ذخیره متن صفحه
                text_file = os.path.join(self.results_dir, "texts", f"{get_domain(url)}_{depth}.txt")
                with open(text_file, "w", encoding="utf-8") as f:
                    f.write(html)
                self.log_link(url, "completed", ct or "", "page", depth)
            else:
                # محتوای غیر HTML (مثلاً فایل مستقیم)
                if raw:
                    cat = categorize_url(url, content_type=ct)
                    fname = unquote(os.path.basename(urlparse(url).path))
                    path, size = self.download_file(url, cat, name=fname)
                    if path:
                        with self.lock:
                            self.total_files += 1
                        self.log_link(url, "downloaded", ct, cat, depth, f"size={size}")
                    else:
                        self.log_link(url, "skipped", ct, cat, depth)
                else:
                    self.log_link(url, "empty/error", ct, "", depth)
        except Exception as e:
            with self.lock:
                self.total_errors += 1
            self.log_link(url, "error", "", "", depth, str(e))

    def run(self):
        send_message(self.chat_id, f"🕸️ خزنده وحشی شروع کرد:\n{self.start_url}")
        # استفاده از ThreadPoolExecutor برای پردازش هم‌زمان صفحات
        # اما همچنان صف را تغذیه می‌کنیم
        with ThreadPoolExecutor(max_workers=5) as executor:
            futures = set()
            # نخ اولیه برای شروع
            while not self.stop_flag and (not self.queue.empty() or futures):
                # ارسال کارهای جدید به تعداد محدود
                while not self.queue.empty() and len(futures) < 5:
                    url, depth = self.queue.get()
                    futures.add(executor.submit(self.process_page, url, depth))
                # بررسی پایان‌یافتن کارها
                done = set()
                for f in futures:
                    if f.done():
                        done.add(f)
                for f in done:
                    futures.remove(f)
                # گزارش لحظه‌ای هر ۲۰ صفحه
                if self.total_pages % 20 == 0 and self.total_pages > 0:
                    msg = f"🔍 {self.total_pages} صفحه بررسی شد | {self.total_files} فایل یافت شد | {self.total_errors} خطا"
                    send_message(self.chat_id, msg)
                time.sleep(0.5)
        # پایان کار
        self._finalize()

    def _finalize(self):
        # گزارش نهایی
        elapsed = time.time() - self.start_time
        summary_lines = []
        summary_lines.append(f"زمان کل: {elapsed:.1f} ثانیه")
        summary_lines.append(f"صفحات پیمایش‌شده: {self.total_pages}")
        summary_lines.append(f"فایل‌های دانلودشده: {self.total_files}")
        summary_lines.append(f"خطاها: {self.total_errors}")
        summary_lines.append(f"حجم کل دانلود: {self.total_size/1024/1024:.2f} MB")
        summary_file = os.path.join(self.results_dir, "summary.txt")
        with open(summary_file, "w", encoding="utf-8") as f:
            f.write("\n".join(summary_lines))
        self.csv_file_handle.close()

        # ایجاد ZIP
        zip_name = f"crawl_result_{uuid.uuid4().hex[:8]}.zip"
        zip_path = os.path.join(self.results_dir, zip_name)
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            for root, dirs, files in os.walk(self.results_dir):
                for file in files:
                    if file.endswith(".zip"): continue
                    file_path = os.path.join(root, file)
                    arcname = os.path.relpath(file_path, self.results_dir)
                    try:
                        zf.write(file_path, arcname)
                    except:
                        pass

        # ارسال به کاربر
        send_message(self.chat_id, "📦 خزنده به پایان رسید. در حال ارسال نتایج...")
        if os.path.getsize(zip_path) > 19 * 1024 * 1024:
            # split and send
            self._send_large_file(zip_path, chat_id=self.chat_id)
        else:
            send_document(self.chat_id, zip_path, caption="🕸️ نتایج خزنده وحشی")

        # پاکسازی (اختیاری - می‌توان دایرکتوری را نگه داشت)
        # shutil.rmtree(self.results_dir, ignore_errors=True)

    def _send_large_file(self, file_path, chat_id):
        # برای سادگی از روش split باینری استفاده می‌کنیم (می‌توانستیم از توابع Bot.py استفاده کنیم،
        # اما برای مستقل بودن K.py یک split ساده اینجا می‌نویسم)
        part_size = 19 * 1024 * 1024
        base = os.path.basename(file_path)
        d = os.path.dirname(file_path)
        with open(file_path, "rb") as f:
            i = 1
            while True:
                chunk = f.read(part_size)
                if not chunk:
                    break
                pname = f"{base}.part{i:03d}"
                ppath = os.path.join(d, pname)
                with open(ppath, "wb") as pf:
                    pf.write(chunk)
                send_document(chat_id, ppath, caption=f"📦 پارت {i}")
                os.remove(ppath)
                i += 1

def start_crawl(chat_id, start_url):
    """نقطه ورود اصلی از Bot.py"""
    crawler = WildCrawler(start_url, chat_id)
    try:
        crawler.run()
    except Exception as e:
        send_message(chat_id, f"❌ خطای کلی در خزنده: {e}")
        traceback.print_exc()

if __name__ == "__main__":
    # برای تست مستقیم
    test_url = "https://example.com"
    start_crawl(123456, test_url)
