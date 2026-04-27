#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
K.py – خزندهٔ وحشی هوشمند (Wild Crawler) – نسخهٔ In‑Memory + لایه‌ای + سه‌حالته
"""

import os, sys, json, time, uuid, hashlib, zipfile, csv, shutil
import requests, threading, queue, traceback
from urllib.parse import urlparse, urljoin, unquote
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from bs4 import BeautifulSoup
from playwright.sync_api import sync_playwright
import re, mimetypes, random

# ═══════ پیکربندی ═══════
BOT_TOKEN = os.getenv("BALE_BOT_TOKEN", "").strip()
if not BOT_TOKEN:
    print("ERROR: BALE_BOT_TOKEN not set", file=sys.stderr)
    sys.exit(1)
BALE_API_URL = f"https://tapi.bale.ai/bot{BOT_TOKEN}"
REQUEST_TIMEOUT = 30

ZIP_PART_SIZE = int(19 * 1024 * 1024)    # 19MB
MAX_TOTAL_DOWNLOAD_SIZE = 2 * 1024 * 1024 * 1024   # ۲ گیگابایت
DOMAIN_DELAY = 1.0

# ═══════ ابزارهای API ═══════
def send_message(chat_id, text, reply_markup=None):
    params = {"chat_id": chat_id, "text": text}
    if reply_markup:
        params["reply_markup"] = json.dumps(reply_markup)
    try:
        r = requests.post(f"{BALE_API_URL}/sendMessage", json=params, timeout=REQUEST_TIMEOUT)
        if r.status_code == 200 and r.json().get("ok"):
            return r.json()["result"]
    except: pass
    return None

def send_document(chat_id, file_path, caption=""):
    if not os.path.exists(file_path): return None
    try:
        with open(file_path, "rb") as f:
            r = requests.post(f"{BALE_API_URL}/sendDocument",
                              data={"chat_id": chat_id, "caption": caption},
                              files={"document": (os.path.basename(file_path), f)},
                              timeout=REQUEST_TIMEOUT * 2)
        if r.status_code == 200 and r.json().get("ok"):
            return r.json()["result"]
    except: pass
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
        for attr in ("href", "src", "data-url", "data-href", "data-link", "data-src", "data-original", "data-lazy"):
            val = tag.get(attr)
            if val:
                try:
                    full = urljoin(base_url, val)
                    if is_valid_url(full): links.add(full)
                except: pass
    for tag in soup.find_all("img"):
        srcset = tag.get("srcset") or ""
        for part in srcset.split(","):
            url_part = part.strip().split(" ")[0]
            if url_part:
                try:
                    full = urljoin(base_url, url_part)
                    if is_valid_url(full): links.add(full)
                except: pass
    for tag in soup.find_all(["picture", "source"]):
        srcset = tag.get("srcset") or ""
        for part in srcset.split(","):
            url_part = part.strip().split(" ")[0]
            if url_part:
                try:
                    full = urljoin(base_url, url_part)
                    if is_valid_url(full): links.add(full)
                except: pass
    for script in soup.find_all("script"):
        if script.string:
            matches = re.findall(r'https?://[^\s"\'<>]+', script.string)
            for m in matches: links.add(m)
    return list(links)

def categorize_url(url, content_type=None):
    path = urlparse(url).path.lower()
    if content_type:
        ct = content_type.lower()
        if "image" in ct: return "image"
        if "video" in ct or "mpegurl" in ct or "dash+xml" in ct: return "video"
        if "application/pdf" in ct: return "pdf"
    if any(path.endswith(ext) for ext in ('.jpg','.jpeg','.png','.gif','.svg','.webp','.bmp','.ico')): return "image"
    if any(path.endswith(ext) for ext in ('.mp4','.mkv','.webm','.avi','.mov','.flv','.wmv')): return "video"
    if any(path.endswith(ext) for ext in ('.m3u8','.mpd')): return "video"
    if path.endswith('.pdf'): return "pdf"
    if any(path.endswith(ext) for ext in ('.zip','.rar','.7z','.tar','.gz','.exe','.apk','.dmg','.iso','.whl','.deb','.rpm')): return "archive"
    return "page"

def get_extension_from_content_type(content_type, default_ext=".file"):
    if not content_type: return default_ext
    ext = mimetypes.guess_extension(content_type.split(";")[0].strip())
    return ext if ext else default_ext

# ═══════ خزنده اصلی ═══════
class WildCrawler:
    def __init__(self, start_url, chat_id, mode="normal", layers=2, limit=0):
        self.start_url = start_url
        self.chat_id = chat_id
        self.visited = set()
        self.queue = queue.Queue()
        self.queue.put((start_url, 0, 1))   # (url, depth, layer)
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
        self.current_layer = 1

        # تنظیمات حالت
        mode_settings = {
            "normal":  {"max_depth": 1, "default_pages": 200, "max_pages_admin": 500,  "max_pages_pro": 200},
            "medium":  {"max_depth": 2, "default_pages": 500, "max_pages_admin": 1000, "max_pages_pro": 400},
            "deep":    {"max_depth": 3, "default_pages": 1200,"max_pages_admin": 2500, "max_pages_pro": 800},
        }
        cfg = mode_settings.get(mode, mode_settings["normal"])
        self.max_depth = min(layers, cfg["max_depth"]) if layers else cfg["max_depth"]
        if limit > 0:
            self.max_pages = limit
        else:
            self.max_pages = cfg["default_pages"]

        # لایه‌های مجاز
        self.max_layers = layers

        # پوشه‌های لایه
        for l in range(1, self.max_layers + 2):   # +2 برای لایه‌های اضافی احتمالی
            layer_dir = os.path.join(self.results_dir, f"layer_{l}")
            for sub in ["images", "videos", "files", "unknown"]:
                os.makedirs(os.path.join(layer_dir, sub), exist_ok=True)

        self.csv_file = os.path.join(self.results_dir, "all_links.csv")
        self._init_csv()

    def _init_csv(self):
        self.csv_file_handle = open(self.csv_file, "w", newline="", encoding="utf-8")
        self.csv_writer = csv.writer(self.csv_file_handle)
        self.csv_writer.writerow(["url", "status", "content_type", "type", "layer", "depth", "note"])

    def log_link(self, url, status, content_type="", typ="", layer=1, depth=0, note=""):
        with self.lock:
            self.csv_writer.writerow([url, status, content_type, typ, layer, depth, note])
            self.csv_file_handle.flush()

    def can_fetch_domain(self, domain):
        now = time.time()
        with self.lock:
            last = self.domain_last_request[domain]
            if now - last < DOMAIN_DELAY:
                time.sleep(DOMAIN_DELAY - (now - last))
            self.domain_last_request[domain] = time.time()

    def fetch_page(self, url):
        headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}
        try:
            self.can_fetch_domain(get_domain(url))
            r = requests.get(url, timeout=30, headers=headers, stream=True)
            content_type = r.headers.get("Content-Type", "")
            if "text/html" not in content_type:
                return None, content_type, r.content
            content = b""
            for chunk in r.iter_content(chunk_size=8192):
                content += chunk
                if len(content) > 5 * 1024 * 1024: break
            return content.decode("utf-8", errors="ignore"), content_type, content
        except: raise

    def download_file(self, url, category, layer, name=None):
        headers = {"User-Agent": "Mozilla/5.0", "Referer": f"{self.start_url}/"}
        try:
            self.can_fetch_domain(get_domain(url))
            # HEAD request for size
            size_est = None
            try:
                head = requests.head(url, timeout=5, headers=headers, allow_redirects=True)
                if "Content-Length" in head.headers:
                    size_est = int(head.headers["Content-Length"])
            except: pass

            with self.lock:
                if self.total_size + (size_est or 0) > MAX_TOTAL_DOWNLOAD_SIZE:
                    return None, 0

            r = requests.get(url, timeout=30, headers=headers, stream=True)
            r.raise_for_status()
            content_type = r.headers.get("Content-Type", "")
            ext = get_extension_from_content_type(content_type)
            if not ext and category == "image": ext = ".jpg"
            if not name:
                name = f"{uuid.uuid4().hex[:8]}{ext}"
            layer_dir = os.path.join(self.results_dir, f"layer_{layer}", category + "s")
            path = os.path.join(layer_dir, name)
            size = 0
            with open(path, "wb") as f:
                for chunk in r.iter_content(8192):
                    if self.stop_flag: return None, 0
                    f.write(chunk)
                    size += len(chunk)
                    with self.lock:
                        if self.total_size + size > MAX_TOTAL_DOWNLOAD_SIZE:
                            os.remove(path)
                            return None, size
            with self.lock:
                self.total_size += size
            return path, size
        except: raise

    def process_page(self, url, depth, layer):
        if self.stop_flag: return
        if depth > self.max_depth: return
        with self.lock:
            if url in self.visited: return
            self.visited.add(url)
            self.total_pages += 1
            if self.total_pages > self.max_pages:
                self.stop_flag = True
                return
            if time.time() - self.start_time > 20 * 60:   # 20 دقیقه حداکثر
                self.stop_flag = True
                return

        self.log_link(url, "processing", "", "page", layer, depth)
        try:
            html, ct, raw = self.fetch_page(url)
            if html:
                links = extract_links_from_html(html, url)
                for link in links:
                    if self.stop_flag: break
                    cat = categorize_url(link)
                    if cat in ("image", "video", "pdf", "archive"):
                        try:
                            fname = unquote(os.path.basename(urlparse(link).path))
                            path, size = self.download_file(link, cat, layer, name=fname)
                            if path:
                                with self.lock: self.total_files += 1
                                self.log_link(link, "downloaded", ct or "", cat, layer, depth, f"size={size}")
                                # Write link to txt
                                txt_file = os.path.join(self.results_dir, f"layer_{layer}", cat + "s_links.txt")
                                with open(txt_file, "a") as lf: lf.write(link + "\n")
                            else:
                                self.log_link(link, "skipped (size limit?)", "", cat, layer, depth)
                        except:
                            with self.lock: self.total_errors += 1
                            self.log_link(link, "error", "", cat, layer, depth, str(sys.exc_info()[1]))
                    else:
                        if depth < self.max_depth and is_same_domain(link, url):
                            self.queue.put((link, depth+1, layer))
                        # اگر لایه فعلی پر نشده و لایه جدید می‌تواند ایجاد شود
                        elif self.total_pages < self.max_pages and layer < self.max_layers + 1:
                            self.queue.put((link, depth+1, layer+1))

                # ذخیره متن صفحه
                text_dir = os.path.join(self.results_dir, f"layer_{layer}", "texts")
                os.makedirs(text_dir, exist_ok=True)
                text_file = os.path.join(text_dir, f"{get_domain(url)}_{depth}.txt")
                with open(text_file, "w", encoding="utf-8") as f: f.write(html)
                self.log_link(url, "completed", ct or "", "page", layer, depth)
            elif raw:
                cat = categorize_url(url, content_type=ct)
                fname = unquote(os.path.basename(urlparse(url).path))
                path, size = self.download_file(url, cat, layer, name=fname)
                if path:
                    with self.lock: self.total_files += 1
                    self.log_link(url, "downloaded", ct, cat, layer, depth, f"size={size}")
                    txt_file = os.path.join(self.results_dir, f"layer_{layer}", cat + "s_links.txt")
                    with open(txt_file, "a") as lf: lf.write(url + "\n")
                else:
                    self.log_link(url, "skipped", ct, cat, layer, depth)
            else:
                self.log_link(url, "empty/error", ct, "", layer, depth)
        except Exception as e:
            with self.lock: self.total_errors += 1
            self.log_link(url, "error", "", "", layer, depth, str(e))

    def run(self):
        send_message(self.chat_id, f"🕸️ خزنده وحشی شروع کرد:\n{self.start_url}\nحالت: {self.max_pages} صفحهٔ مجاز | لایه‌ها: {self.max_layers}")
        with ThreadPoolExecutor(max_workers=5) as executor:
            futures = set()
            while not self.stop_flag and (not self.queue.empty() or futures):
                while not self.queue.empty() and len(futures) < 5:
                    url, depth, layer = self.queue.get()
                    futures.add(executor.submit(self.process_page, url, depth, layer))
                done = {f for f in futures if f.done()}
                for f in done: futures.remove(f)
                if self.total_pages % 20 == 0 and self.total_pages > 0:
                    send_message(self.chat_id, f"🔍 {self.total_pages} صفحه بررسی شد | {self.total_files} فایل یافت شد | {self.total_errors} خطا")
                time.sleep(0.5)
        self._finalize()

    def _finalize(self):
        elapsed = time.time() - self.start_time
        summary_lines = [
            f"زمان کل: {elapsed:.1f} ثانیه",
            f"صفحات پیمایش‌شده: {self.total_pages}",
            f"فایل‌های دانلودشده: {self.total_files}",
            f"خطاها: {self.total_errors}",
            f"حجم کل دانلود: {self.total_size/1024/1024:.2f} MB",
        ]
        with open(os.path.join(self.results_dir, "summary.txt"), "w", encoding="utf-8") as f:
            f.write("\n".join(summary_lines))
        self.csv_file_handle.close()

        # ZIP
        zip_name = f"crawl_result_{uuid.uuid4().hex[:8]}.zip"
        zip_path = os.path.join(self.results_dir, zip_name)
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            for root, dirs, files in os.walk(self.results_dir):
                for file in files:
                    if file.endswith(".zip"): continue
                    fp = os.path.join(root, file)
                    arcname = os.path.relpath(fp, self.results_dir)
                    zf.write(fp, arcname)

        send_message(self.chat_id, "📦 خزنده به پایان رسید. در حال ارسال نتایج...")
        if os.path.getsize(zip_path) > ZIP_PART_SIZE:
            self._send_large_file(zip_path)
        else:
            send_document(self.chat_id, zip_path, caption="🕸️ نتایج خزنده وحشی")
        shutil.rmtree(self.results_dir, ignore_errors=True)

    def _send_large_file(self, file_path):
        part_size = ZIP_PART_SIZE
        base = os.path.basename(file_path)
        d = os.path.dirname(file_path)
        parts = []
        with open(file_path, "rb") as f:
            i = 1
            while True:
                chunk = f.read(part_size)
                if not chunk: break
                pname = f"{base}.part{i:03d}"
                ppath = os.path.join(d, pname)
                with open(ppath, "wb") as pf: pf.write(chunk)
                parts.append(ppath)
                i += 1
        merge_text = "همهٔ فایل‌ها را دانلود کنید، سپس فایل .part001 را با WinRAR یا 7-Zip باز کنید."
        merge_path = os.path.join(d, "merge.txt")
        with open(merge_path, "w") as f: f.write(merge_text)
        send_document(self.chat_id, merge_path, caption="📝 راهنما")
        for idx, p in enumerate(parts, 1):
            send_document(self.chat_id, p, caption=f"📦 پارت {idx}/{len(parts)}")
        os.remove(merge_path)

def start_crawl(chat_id, start_url, mode="normal", layers=2, limit=0):
    crawler = WildCrawler(start_url, chat_id, mode, layers, limit)
    try:
        crawler.run()
    except Exception as e:
        send_message(chat_id, f"❌ خطای کلی در خزنده: {e}")
        traceback.print_exc()

if __name__ == "__main__":
    start_crawl(123456, "https://example.com", "normal", 2, 0)
