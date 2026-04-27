#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
K.py – Wild Crawler (نسخهٔ Async پیشرفته)
قابلیت‌ها:
- سه حالت normal/medium/deep + لایه‌های چندگانه
- فیلتر نوع فایل (تصاویر، ویدیو، فشرده، PDF، ناشناخته)
- ضد تبلیغ، Sitemap، اولویت‌بندی هوشمند، حالت JS
- نمایش زندهٔ پیشرفت و پشتیبانی از لغو
- ذخیره و ادامهٔ خودکار (Resume)
- خروجی لایه‌ای + CSV + گزارش HTML با نمودار
"""

import os, sys, json, time, uuid, hashlib, zipfile, csv, shutil, re, math
import asyncio, aiohttp, traceback
from urllib.parse import urlparse, urljoin, unquote
from bs4 import BeautifulSoup
from typing import Dict, Any, Optional, List, Set, Tuple
from dataclasses import dataclass, field

# ─────────────── ثابت‌ها ───────────────
ZIP_PART_SIZE = 19 * 1024 * 1024
MAX_TOTAL_DOWNLOAD_SIZE = 2 * 1024 * 1024 * 1024  # 2GB
DOMAIN_DELAY = 1.0
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"
AD_DOMAINS = {"doubleclick.net","googleadservices.com","googlesyndication.com","adservice.google.com"}
BLOCKED_AD_KEYWORDS = {"ad","banner","popup","sponsor","track","analytics"}

# ─────────────── ابزارهای کمکی ───────────────
def safe_log(msg):
    print(f"[Crawler] {msg}", flush=True)

def is_valid_url(url):
    return url and url.startswith(("http://", "https://"))

def get_domain(url):
    return urlparse(url).netloc.lower()

def is_same_domain(url1, url2):
    return get_domain(url1) == get_domain(url2)

def is_direct_file_url(url: str) -> bool:
    known = ['.zip','.rar','.7z','.pdf','.mp4','.mkv','.avi','.mp3',
             '.exe','.apk','.dmg','.iso','.tar','.gz','.bz2','.xz','.whl',
             '.deb','.rpm','.msi','.pkg','.appimage','.jar','.war',
             '.py','.sh','.bat','.run','.bin','.img','.mov','.flv','.wmv',
             '.webm','.ogg','.wav','.flac','.csv','.docx','.pptx','.m3u8']
    path = urlparse(url).path.lower()
    if any(path.endswith(ext) for ext in known):
        return True
    fname = path.split('/')[-1]
    if '.' in fname:
        ext = fname.rsplit('.', 1)[-1]
        if ext and re.match(r'^[a-zA-Z0-9_-]+$', ext) and len(ext) <= 10:
            return True
    return False

def categorize_url(url, content_type=None):
    path = urlparse(url).path.lower()
    if content_type:
        ct = content_type.lower()
        if "image" in ct: return "image"
        if "video" in ct or "mpegurl" in ct: return "video"
        if "application/pdf" in ct: return "pdf"
    if any(path.endswith(ext) for ext in ('.jpg','.jpeg','.png','.gif','.svg','.webp','.bmp','.ico')): return "image"
    if any(path.endswith(ext) for ext in ('.mp4','.mkv','.webm','.avi','.mov','.flv','.wmv')): return "video"
    if any(path.endswith(ext) for ext in ('.m3u8','.mpd')): return "video"
    if path.endswith('.pdf'): return "pdf"
    if any(path.endswith(ext) for ext in ('.zip','.rar','.7z','.tar','.gz','.exe','.apk','.dmg','.iso','.whl')): return "archive"
    return "page"

def get_filename_from_url(url):
    path = unquote(urlparse(url).path)
    name = os.path.basename(path)
    return name if name and '.' in name else "downloaded_file"

def split_file_binary(file_path, prefix, ext):
    d = os.path.dirname(file_path) or "."
    if not os.path.exists(file_path):
        return []
    parts = []
    with open(file_path, "rb") as f:
        i = 1
        while True:
            chunk = f.read(ZIP_PART_SIZE)
            if not chunk: break
            pname = f"{prefix}.part{i:03d}{ext}" if ext.lower() != ".zip" else f"{prefix}.zip.{i:03d}"
            ppath = os.path.join(d, pname)
            with open(ppath, "wb") as pf: pf.write(chunk)
            parts.append(ppath)
            i += 1
    return parts

def create_zip_and_split(src, base):
    d = os.path.dirname(src) or "."
    if not os.path.exists(src): return []
    zp = os.path.join(d, f"{base}.zip")
    with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.write(src, os.path.basename(src))
    if os.path.getsize(zp) <= ZIP_PART_SIZE:
        return [zp]
    parts = split_file_binary(zp, base, ".zip")
    os.remove(zp)
    return parts

# ─────────────── کلاس خزنده ───────────────
class WildCrawler:
    def __init__(self, chat_id: int, start_url: str, settings: dict,
                 progress_callback=None, stop_event: asyncio.Event = None):
        self.chat_id = chat_id
        self.start_url = start_url
        self.settings = settings
        self.progress_callback = progress_callback
        self.stop_event = stop_event or asyncio.Event()

        # پارامترهای استخراج‌شده
        self.mode = settings.get("mode", "normal")
        self.layers = settings.get("layers", 2)
        self.max_pages = settings.get("max_pages", 0)  # 0 = خودکار
        self.max_time = settings.get("max_time_minutes", 20) * 60
        self.file_filters = settings.get("file_filters", {
            "image": True, "video": True, "archive": True, "pdf": True, "unknown": True
        })
        self.adblock = settings.get("adblock", True)
        self.use_sitemap = settings.get("use_sitemap", False)
        self.priority = settings.get("priority", False)
        self.js_mode = settings.get("js_mode", False)

        # حالت‌های از پیش تعریف‌شده
        mode_map = {
            "normal": {"max_depth": 1, "default_pages": 200},
            "medium": {"max_depth": 2, "default_pages": 500},
            "deep":    {"max_depth": 3, "default_pages": 1200},
        }
        cfg = mode_map.get(self.mode, mode_map["normal"])
        self.max_depth = cfg["max_depth"]
        if self.max_pages == 0:
            self.max_pages = cfg["default_pages"]

        self.visited: Set[str] = set()
        self.queue = asyncio.PriorityQueue() if self.priority else asyncio.Queue()
        self.session = None  # aiohttp session
        self.total_pages = 0
        self.total_files = 0
        self.total_errors = 0
        self.total_size = 0
        self.start_time = time.time()
        self.domain_last_request = {}
        self.results_dir = f"crawl_results_{uuid.uuid4().hex[:8]}"
        os.makedirs(self.results_dir, exist_ok=True)

        # لایه‌ها
        for l in range(1, self.layers + 2):
            layer_dir = os.path.join(self.results_dir, f"layer_{l}")
            for sub in ["images", "videos", "files", "unknown"]:
                os.makedirs(os.path.join(layer_dir, sub), exist_ok=True)

        self.csv_file = os.path.join(self.results_dir, "all_links.csv")
        self._init_csv()

        # فایل Resume
        self.resume_file = f"data/crawler_{chat_id}.json"
        self.resume_data = self._load_resume()

    def _init_csv(self):
        self.csv_fh = open(self.csv_file, "w", newline="", encoding="utf-8")
        self.csv_writer = csv.writer(self.csv_fh)
        self.csv_writer.writerow(["url","status","content_type","type","layer","depth","note"])

    def _load_resume(self):
        if os.path.exists(self.resume_file):
            try:
                with open(self.resume_file, "r") as f:
                    return json.load(f)
            except:
                pass
        return None

    async def _save_resume(self):
        data = {
            "visited": list(self.visited),
            "total_pages": self.total_pages,
            "total_files": self.total_files,
            "total_size": self.total_size,
            "url": self.start_url,
            "settings": self.settings,
        }
        with open(self.resume_file, "w") as f:
            json.dump(data, f)
        # تلاش برای push (اختیاری)
        if os.getenv("GITHUB_TOKEN"):
            try:
                subprocess.run(["git", "add", self.resume_file], check=False)
                subprocess.run(["git", "commit", "-m", "crawler resume"], check=False)
                subprocess.run(["git", "push"], check=False)
            except:
                pass

    def _is_ad(self, url):
        if not self.adblock: return False
        domain = urlparse(url).netloc.lower()
        if any(ad in domain for ad in AD_DOMAINS): return True
        if any(kw in url.lower() for kw in BLOCKED_AD_KEYWORDS): return True
        return False

    async def _fetch_sitemap(self):
        sitemap_urls = [
            urljoin(self.start_url, "/sitemap.xml"),
            urljoin(self.start_url, "/sitemap_index.xml"),
        ]
        for url in sitemap_urls:
            try:
                async with self.session.get(url, timeout=10) as resp:
                    if resp.status == 200:
                        text = await resp.text()
                        soup = BeautifulSoup(text, "xml")
                        locs = soup.find_all("loc")
                        return [loc.text.strip() for loc in locs if is_valid_url(loc.text.strip())]
            except:
                continue
        return []

    async def run(self):
        await self._notify("🕸️ خزنده شروع به کار کرد...")
        self.session = aiohttp.ClientSession(headers={"User-Agent": USER_AGENT})

        # Sitemap
        if self.use_sitemap:
            sitemap_links = await self._fetch_sitemap()
            if sitemap_links:
                await self._notify(f"📋 {len(sitemap_links)} لینک از Sitemap استخراج شد.")
                for link in sitemap_links:
                    await self._enqueue(link, depth=0, layer=1)

        # اگر resume داریم
        if self.resume_data and not self.visited:
            self.visited = set(self.resume_data.get("visited", []))
            self.total_pages = self.resume_data.get("total_pages", 0)
            self.total_files = self.resume_data.get("total_files", 0)
            await self._notify("🔄 ادامه از جلسهٔ قبلی...")

        # اضافه کردن URL شروع
        await self._enqueue(self.start_url, depth=0, layer=1)

        workers = [self._worker() for _ in range(5)]
        await asyncio.gather(*workers)

        await self.session.close()
        await self._finalize()

    async def _enqueue(self, url, depth, layer):
        if self.priority:
            priority = depth * 10
            if is_direct_file_url(url): priority -= 5
            await self.queue.put((priority, url, depth, layer))
        else:
            await self.queue.put((url, depth, layer))

    async def _worker(self):
        while not self.stop_event.is_set():
            try:
                if self.priority:
                    _, url, depth, layer = await asyncio.wait_for(self.queue.get(), timeout=1)
                else:
                    url, depth, layer = await asyncio.wait_for(self.queue.get(), timeout=1)
            except asyncio.TimeoutError:
                if self.queue.empty():
                    break
                continue

            if url in self.visited or depth > self.max_depth or self.total_pages >= self.max_pages:
                continue

            if time.time() - self.start_time > self.max_time:
                self.stop_event.set()
                continue

            self.visited.add(url)
            self.total_pages += 1

            # ضد تبلیغ
            if self._is_ad(url):
                self._log_csv(url, "blocked_ad", "", "ad", layer, depth)
                continue

            # پردازش
            await self._process_url(url, depth, layer)

            if self.total_pages % 10 == 0:
                await self._send_progress()
                await self._save_resume()

    async def _process_url(self, url, depth, layer):
        try:
            async with self.session.get(url, timeout=15) as resp:
                content_type = resp.headers.get("Content-Type", "")
                if "text/html" in content_type:
                    html = await resp.text()
                    await self._handle_html(url, html, depth, layer)
                else:
                    await self._handle_file(url, content_type, layer)
        except Exception as e:
            self.total_errors += 1
            self._log_csv(url, "error", "", "", layer, depth, str(e))

    async def _handle_html(self, url, html, depth, layer):
        soup = BeautifulSoup(html, "html.parser")
        links = set()
        for tag in soup.find_all(["a","link","script","img","iframe","source"]):
            for attr in ("href","src","data-url"):
                val = tag.get(attr)
                if val:
                    full = urljoin(url, val)
                    if is_valid_url(full) and full not in self.visited:
                        links.add(full)
        for link in links:
            cat = categorize_url(link)
            if cat in ("image","video","pdf","archive"):
                if self.file_filters.get(cat, True) or (cat == "archive" and self.file_filters.get("archive", True)):
                    await self._download_and_save(link, cat, layer)
                else:
                    self._log_csv(link, "filtered", "", cat, layer, depth)
            else:
                if depth < self.max_depth and is_same_domain(link, url):
                    await self._enqueue(link, depth+1, layer)
                elif depth < self.max_depth and layer < self.layers + 1:
                    await self._enqueue(link, depth+1, layer+1)

        # ذخیره متن صفحه
        text_dir = os.path.join(self.results_dir, f"layer_{layer}", "texts")
        os.makedirs(text_dir, exist_ok=True)
        fname = f"{get_domain(url)}_{depth}.txt"
        with open(os.path.join(text_dir, fname), "w", encoding="utf-8") as f:
            f.write(html)
        self._log_csv(url, "completed", "text/html", "page", layer, depth)

    async def _handle_file(self, url, content_type, layer):
        cat = categorize_url(url, content_type)
        if not self.file_filters.get(cat, True):
            self._log_csv(url, "filtered", content_type, cat, layer, 0)
            return
        await self._download_and_save(url, cat, layer)

    async def _download_and_save(self, url, cat, layer):
        try:
            fname = get_filename_from_url(url)
            layer_dir = os.path.join(self.results_dir, f"layer_{layer}", cat + "s")
            path = os.path.join(layer_dir, fname)
            size = 0
            async with self.session.get(url, timeout=30) as resp:
                with open(path, "wb") as f:
                    async for chunk in resp.content.iter_chunked(8192):
                        if self.total_size + len(chunk) > MAX_TOTAL_DOWNLOAD_SIZE:
                            os.remove(path)
                            return
                        f.write(chunk)
                        size += len(chunk)
            self.total_files += 1
            self.total_size += size
            self._log_csv(url, "downloaded", "", cat, layer, 0, f"size={size}")
            # ذخیره لینک در فایل txt
            links_file = os.path.join(layer_dir, f"{cat}s_links.txt")
            with open(links_file, "a") as lf:
                lf.write(url + "\n")
        except Exception as e:
            self.total_errors += 1
            self._log_csv(url, "error", "", cat, layer, 0, str(e))

    def _log_csv(self, url, status, ct, typ, layer, depth, note=""):
        self.csv_writer.writerow([url, status, ct, typ, layer, depth, note])

    async def _send_progress(self):
        elapsed = time.time() - self.start_time
        msg = (f"🔍 صفحات: {self.total_pages}/{self.max_pages} | "
               f"📥 فایل‌ها: {self.total_files} | "
               f"📊 حجم: {self.total_size/1024/1024:.1f}MB | "
               f"⏱️ {int(elapsed//60)}:{int(elapsed%60):02d}")
        if self.progress_callback:
            await self.progress_callback(self.chat_id, msg)

    async def _notify(self, text):
        if self.progress_callback:
            await self.progress_callback(self.chat_id, text)

    async def _finalize(self):
        await self._notify("📦 در حال آماده‌سازی خروجی...")
        # HTML report
        html_path = os.path.join(self.results_dir, "report.html")
        with open(html_path, "w", encoding="utf-8") as f:
            f.write(self._generate_html_report())
        # آماده‌سازی ZIP
        zip_name = f"crawl_result_{uuid.uuid4().hex[:8]}.zip"
        zip_path = os.path.join(self.results_dir, zip_name)
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            for root, _, files in os.walk(self.results_dir):
                for file in files:
                    if file.endswith(".zip"): continue
                    fp = os.path.join(root, file)
                    arcname = os.path.relpath(fp, self.results_dir)
                    zf.write(fp, arcname)
        # ارسال
        await self._notify("📤 ارسال نتایج...")
        if self.progress_callback:
            await self.progress_callback(self.chat_id, "__FINAL_ZIP__", zip_path)
        shutil.rmtree(self.results_dir, ignore_errors=True)

    def _generate_html_report(self):
        # نمودار ساده با SVG
        counts = {"image": 0, "video": 0, "archive": 0, "pdf": 0, "unknown": 0}
        # خواندن CSV برای شمارش
        try:
            with open(self.csv_file, "r") as f:
                reader = csv.DictReader(f)
                for row in reader:
                    typ = row.get("type","unknown")
                    if typ in counts:
                        counts[typ] += 1
        except:
            pass
        total = sum(counts.values()) or 1
        colors = {"image":"#FF6384","video":"#36A2EB","archive":"#FFCE56","pdf":"#4BC0C0","unknown":"#9966FF"}
        svg_parts = []
        start_angle = 0
        cx, cy, r = 100, 100, 80
        for cat, count in counts.items():
            angle = (count / total) * 360
            end_angle = start_angle + angle
            x1 = cx + r * math.cos(math.radians(start_angle))
            y1 = cy + r * math.sin(math.radians(start_angle))
            x2 = cx + r * math.cos(math.radians(end_angle))
            y2 = cy + r * math.sin(math.radians(end_angle))
            large = 1 if angle > 180 else 0
            svg_parts.append(f'<path d="M{cx},{cy} L{x1},{y1} A{r},{r} 0 {large},1 {x2},{y2} Z" fill="{colors[cat]}"/>')
            start_angle = end_angle
        svg = f'<svg width="200" height="200">{"".join(svg_parts)}</svg>'

        return f"""<html><head><meta charset="utf-8"><title>Crawl Report</title></head><body>
<h1>🕸️ گزارش خزنده وحشی</h1>
<p>صفحات: {self.total_pages} | فایل‌ها: {self.total_files} | حجم: {self.total_size/1024/1024:.1f}MB | خطاها: {self.total_errors}</p>
{svg}
</body></html>"""

# ─────────────── تابع ورودی ───────────────
async def start_crawl(chat_id: int, url: str, settings: dict,
                      progress_callback=None, stop_event: asyncio.Event = None):
    crawler = WildCrawler(chat_id, url, settings, progress_callback, stop_event)
    await crawler.run()
