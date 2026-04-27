#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Bot27 – In-Memory Edition (پایدار نهایی)
"""

import os, sys, json, time, math, queue, shutil, zipfile, uuid, re, hashlib
import subprocess, threading, traceback
from dataclasses import dataclass, asdict, field
from typing import Dict, Any, Optional, List, Tuple
from urllib.parse import urlparse, urljoin, unquote

import requests
from bs4 import BeautifulSoup
from playwright.sync_api import sync_playwright

# ═══════════════ پیکربندی ═══════════════
BALE_BOT_TOKEN = os.getenv("BALE_BOT_TOKEN", "").strip()
if not BALE_BOT_TOKEN:
    print("ERROR: BALE_BOT_TOKEN not set", file=sys.stderr)
    sys.exit(1)

BALE_API_URL = "https://tapi.bale.ai/bot" + BALE_BOT_TOKEN
REQUEST_TIMEOUT = 30
LONG_POLL_TIMEOUT = 50
ZIP_PART_SIZE = int(19 * 1024 * 1024)

ADMIN_CHAT_ID = 46829437

WORKER_TIMEOUT = 300
MAX_RECORD_MINUTES_ADMIN = 60
MAX_RECORD_MINUTES_USER = 15
MAX_4K_RECORD_MINUTES = 10

# ═══════════════ سطوح اشتراک ═══════════════
PLAN_LIMITS = {
    "پایه": {
        "browser": (3, 3600, None), "screenshot": (3, 3600, None),
        "2x_screenshot": (0, 3600, None), "4k_screenshot": (0, 3600, None),
        "download": (1, 3600, 20 * 1024 * 1024), "record_video": (0, 3600, None),
        "scan_downloads": (0, 3600, None), "scan_videos": (0, 3600, None),
        "download_website": (0, 3600, None), "extract_commands": (0, 3600, None),
        "interactive_scan": (0, 3600, None), "fullpage_screenshot": (0, 3600, None),
    },
    "نقره‌ای": {
        "browser": (5, 3600, None), "screenshot": (5, 3600, None),
        "2x_screenshot": (1, 3600, None), "4k_screenshot": (0, 3600, None),
        "download": (3, 3600, 100 * 1024 * 1024), "record_video": (2, 3600, None),
        "scan_downloads": (1, 3600, None), "scan_videos": (1, 3600, None),
        "download_website": (0, 3600, None), "extract_commands": (1, 3600, None),
        "interactive_scan": (1, 3600, None), "fullpage_screenshot": (1, 3600, None),
    },
    "طلایی": {
        "browser": (15, 3600, None), "screenshot": (15, 3600, None),
        "2x_screenshot": (5, 3600, None), "4k_screenshot": (0, 3600, None),
        "download": (10, 3600, 600 * 1024 * 1024), "record_video": (8, 3600, None),
        "scan_downloads": (5, 3600, None), "scan_videos": (8, 3600, None),
        "download_website": (2, 3600, None), "extract_commands": (5, 3600, None),
        "interactive_scan": (5, 3600, None), "fullpage_screenshot": (5, 3600, None),
    },
    "الماسی": {
        "browser": (30, 3600, None), "screenshot": (30, 3600, None),
        "2x_screenshot": (20, 3600, None), "4k_screenshot": (5, 3600, None),
        "download": (20, 3600, 2 * 1024 * 1024 * 1024), "record_video": (12, 3600, None),
        "scan_downloads": (15, 3600, None), "scan_videos": (20, 3600, None),
        "download_website": (5, 86400, None), "extract_commands": (20, 3600, None),
        "interactive_scan": (20, 3600, None), "fullpage_screenshot": (20, 3600, None),
    },
}

ALLOWED_RESOLUTIONS = {
    "480p": (854, 480), "720p": (1280, 720),
    "1080p": (1920, 1080), "4k": (3840, 2160),
}
RES_REQUIREMENTS = {
    "480p": ["پایه", "نقره‌ای", "طلایی", "الماسی"],
    "720p": ["نقره‌ای", "طلایی", "الماسی"],
    "1080p": ["طلایی", "الماسی"],
    "4k": ["الماسی"],
}

AD_DOMAINS = {"doubleclick.net", "googleadservices.com", "googlesyndication.com", "adservice.google.com"}
BLOCKED_AD_KEYWORDS = {"ad", "banner", "popup", "sponsor", "track", "analytics"}

# ═══════════════ کدهای اشتراک هاردکد ═══════════════
HARDCODED_CODES = {
    "نقره‌ای": [
        "SIL-001","SIL-002","SIL-003","SIL-004","SIL-005",
        "SIL-006","SIL-007","SIL-008","SIL-009","SIL-010",
        "SIL-011","SIL-012","SIL-013","SIL-014","SIL-015",
        "SIL-016","SIL-017","SIL-018","SIL-019","SIL-020"
    ],
    "طلایی": [
        "GLD-001","GLD-002","GLD-003","GLD-004","GLD-005",
        "GLD-006","GLD-007","GLD-008","GLD-009","GLD-010",
        "GLD-011","GLD-012","GLD-013","GLD-014","GLD-015",
        "GLD-016","GLD-017","GLD-018","GLD-019","GLD-020"
    ],
    "الماسی": [
        "DIA-001","DIA-002","DIA-003","DIA-004","DIA-005",
        "DIA-006","DIA-007","DIA-008","DIA-009","DIA-010",
        "DIA-011","DIA-012","DIA-013","DIA-014","DIA-015",
        "DIA-016","DIA-017","DIA-018","DIA-019","DIA-020"
    ]
}
code_bindings: Dict[str, int] = {}

# ═══════════════ قفل‌ها و ساختارهای In-Memory ═══════════════
print_lock = threading.Lock()
callback_map: Dict[str, str] = {}
callback_map_lock = threading.Lock()
flood_lock = threading.Lock()
user_flood_data: Dict[int, List[float]] = {}
user_ban_until: Dict[int, float] = {}
admin_bans: Dict[int, float] = {}

queue_locks = {
    "browser": threading.Lock(),
    "download": threading.Lock(),
    "record": threading.Lock()
}
inmemory_queues = {
    "browser": [],
    "download": [],
    "record": []
}

inmemory_sessions: Dict[str, Dict[str, Any]] = {}
inmemory_subscriptions: Dict[int, str] = {}
service_disabled = False

def safe_print(*args, **kwargs):
    with print_lock:
        print(*args, **kwargs, flush=True)

# ═══════════════ مدل‌های داده ═══════════════
@dataclass
class UserSettings:
    record_time: int = 20
    default_download_mode: str = "store"
    browser_mode: str = "text"
    deep_scan_mode: str = "logical"
    record_behavior: str = "click"
    audio_enabled: bool = False
    video_format: str = "webm"
    incognito_mode: bool = False
    video_delivery: str = "split"
    video_resolution: str = "720p"
    crawler_mode: str = "normal"
    crawler_layers: int = 2
    crawler_limit: int = 0

@dataclass
class SessionState:
    chat_id: int
    state: str = "idle"
    is_admin: bool = False
    subscription: str = "پایه"
    current_job_id: Optional[str] = None
    browser_url: Optional[str] = None
    last_interaction: float = time.time()
    cancel_requested: bool = False
    text_links: Dict[str, str] = field(default_factory=dict)
    browser_links: Optional[List[Dict[str, str]]] = None
    browser_page: int = 0
    settings: UserSettings = field(default_factory=UserSettings)
    click_counter: int = 0
    ad_blocked_domains: List[str] = field(default_factory=list)
    found_downloads: Optional[List[Dict[str, str]]] = None
    found_downloads_page: int = 0
    last_settings_msg_id: Optional[str] = None
    interactive_elements: Optional[List[Dict[str, Any]]] = None
    stop_requested: bool = False
    last_browser_time: float = 0.0
    crawler_active: bool = False
    usage: Dict[str, List[float]] = field(default_factory=dict)

@dataclass
class Job:
    job_id: str
    chat_id: int
    mode: str
    url: str
    status: str = "queued"
    created_at: float = time.time()
    updated_at: float = time.time()
    error_message: Optional[str] = None
    extra: Optional[Dict[str, Any]] = None
    started_at: Optional[float] = None
    queue_type: str = "browser"
    stop_flag: bool = False

# ═══════════════ مدیریت Ban ═══════════════
def ban_user(chat_id: int, minutes: Optional[int] = None):
    now = time.time()
    with flood_lock:
        if minutes is None:
            admin_bans[chat_id] = 9999999999
        else:
            admin_bans[chat_id] = now + minutes * 60

def unban_user(chat_id: int):
    with flood_lock:
        if chat_id in admin_bans:
            del admin_bans[chat_id]
            return True
        return False

def is_user_banned(chat_id: int) -> bool:
    if chat_id == ADMIN_CHAT_ID:
        return False
    now = time.time()
    with flood_lock:
        if chat_id in admin_bans and now < admin_bans[chat_id]:
            return True
        if chat_id in admin_bans:
            del admin_bans[chat_id]
        if chat_id in user_ban_until and now < user_ban_until[chat_id]:
            return True
        return False

# ═══════════════ اشتراک‌ها ═══════════════
def get_user_subscription(chat_id: int) -> str:
    return inmemory_subscriptions.get(chat_id, "پایه")

def set_user_subscription(chat_id: int, level: str):
    inmemory_subscriptions[chat_id] = level

def activate_subscription(chat_id: int, code: str) -> Optional[str]:
    code = code.strip()
    for plan, codes in HARDCODED_CODES.items():
        if code in codes:
            if code in code_bindings and code_bindings[code] != chat_id:
                return None
            code_bindings[code] = chat_id
            set_user_subscription(chat_id, plan)
            return plan
    return None

def is_service_disabled() -> bool:
    return service_disabled

def toggle_service():
    global service_disabled
    service_disabled = not service_disabled
    return service_disabled

# ═══════════════ Rate Limiter ═══════════════
def check_rate_limit(chat_id: int, mode: str, file_size_bytes: Optional[int] = None) -> Optional[str]:
    if chat_id == ADMIN_CHAT_ID:
        return None
    level = get_user_subscription(chat_id)
    limits = PLAN_LIMITS.get(level, PLAN_LIMITS["پایه"])
    mode_key = mode
    if mode in ("browser", "browser_click"):
        mode_key = "browser"
    limit = limits.get(mode_key)
    if not limit:
        return f"⛔ این قابلیت برای سطح «{level}» در دسترس نیست."
    max_count, window_seconds, max_size = limit
    if max_size is not None and file_size_bytes is not None and file_size_bytes > max_size:
        max_mb = max_size / (1024 * 1024)
        return f"📦 حجم فایل ({file_size_bytes/(1024*1024):.1f}MB) بیش از حد مجاز ({max_mb:.0f}MB) برای سطح «{level}» است."
    if max_count >= 999:
        return None
    now = time.time()
    sess = get_session(chat_id)
    usage = sess.usage.get(mode_key, [])
    cutoff = now - window_seconds
    recent = [t for t in usage if t > cutoff]
    if len(recent) >= max_count:
        return f"⏰ محدودیت ساعتی: حداکثر {max_count} بار در ساعت (سطح «{level}»)."
    usage.append(time.time())
    sess.usage[mode_key] = usage
    set_session(sess)
    return None

# ═══════════════ ضد اسپم ═══════════════
FLOOD_WINDOW = 5
FLOOD_MAX_CLICKS = 10
BAN_DURATION = 900

def check_flood(chat_id: int) -> bool:
    if chat_id == ADMIN_CHAT_ID:
        return True
    now = time.time()
    with flood_lock:
        if is_user_banned(chat_id):
            return False
        clicks = user_flood_data.get(chat_id, [])
        clicks = [t for t in clicks if now - t < FLOOD_WINDOW]
        clicks.append(now)
        user_flood_data[chat_id] = clicks
        if len(clicks) > FLOOD_MAX_CLICKS:
            user_ban_until[chat_id] = now + BAN_DURATION
            return False
        return True

# ═══════════════ نشست‌ها ═══════════════
def get_session(chat_id):
    key = str(chat_id)
    if key in inmemory_sessions:
        s = SessionState(chat_id=chat_id)
        d = inmemory_sessions[key]
        for k, v in d.items():
            if k == "settings":
                s.settings = UserSettings(**v)
            elif k in ("ad_blocked_domains", "found_downloads", "last_settings_msg_id", "interactive_elements", "usage"):
                setattr(s, k, v)
            else:
                setattr(s, k, v)
        if s.chat_id == ADMIN_CHAT_ID:
            s.is_admin = True
            s.subscription = "الماسی"
        else:
            s.subscription = get_user_subscription(chat_id)
        return s
    s = SessionState(chat_id=chat_id)
    if s.chat_id == ADMIN_CHAT_ID:
        s.is_admin = True
        s.subscription = "الماسی"
    return s

def set_session(session):
    d = asdict(session)
    d["settings"] = asdict(session.settings)
    d["ad_blocked_domains"] = session.ad_blocked_domains
    d["found_downloads"] = session.found_downloads
    d["last_settings_msg_id"] = session.last_settings_msg_id
    d["interactive_elements"] = session.interactive_elements
    d["usage"] = session.usage
    inmemory_sessions[str(session.chat_id)] = d

# ═══════════════ API بله ═══════════════
def bale_request(method, params=None, files=None):
    url = f"{BALE_API_URL}/{method}"
    try:
        if files:
            r = requests.post(url, data=params or {}, files=files, timeout=REQUEST_TIMEOUT)
        else:
            r = requests.post(url, json=params or {}, timeout=REQUEST_TIMEOUT)
        if method == "getUpdates":
            safe_print(f"[API] getUpdates -> HTTP {r.status_code}, ok={r.json().get('ok')}, result count={len(r.json().get('result', []))}")
        elif r.status_code != 200 or not r.json().get("ok"):
            safe_print(f"[API] {method} -> HTTP {r.status_code}, ok={r.json().get('ok')}, response={r.text[:200]}")
        if r.status_code != 200:
            return None
        data = r.json()
        if not data.get("ok"):
            return None
        return data["result"]
    except Exception as e:
        safe_print(f"[API] {method} -> EXCEPTION: {e}")
        return None

def send_message(chat_id, text, reply_markup=None):
    params = {"chat_id": chat_id, "text": text}
    if reply_markup:
        params["reply_markup"] = json.dumps(reply_markup)
    return bale_request("sendMessage", params=params)

def edit_message_reply_markup(chat_id, message_id, reply_markup):
    params = {"chat_id": chat_id, "message_id": message_id, "reply_markup": json.dumps(reply_markup)}
    return bale_request("editMessageReplyMarkup", params=params)

def send_document(chat_id, file_path, caption=""):
    if not os.path.exists(file_path):
        return None
    with open(file_path, "rb") as f:
        return bale_request("sendDocument",
                            params={"chat_id": chat_id, "caption": caption},
                            files={"document": (os.path.basename(file_path), f)})

def answer_callback_query(cq_id, text="", show_alert=False):
    return bale_request("answerCallbackQuery",
                        {"callback_query_id": cq_id, "text": text, "show_alert": show_alert})

def get_updates(offset=None, timeout=LONG_POLL_TIMEOUT):
    params = {"timeout": timeout}
    if offset:
        params["offset"] = offset
    safe_print(f"[Poll] asking with offset={offset}, timeout={timeout}")
    result = bale_request("getUpdates", params=params)
    if result:
        safe_print(f"[Poll] got {len(result)} updates")
    else:
        safe_print(f"[Poll] got None/[] from server")
    return result or []

# ═══════════════ منوها ═══════════════
def main_menu_keyboard(is_admin=False):
    base = [
        [{"text": "🧭 مرورگر", "callback_data": "menu_browser"},
         {"text": "📸 شات", "callback_data": "menu_screenshot"}],
        [{"text": "📥 دانلود", "callback_data": "menu_download"},
         {"text": "🎬 ضبط", "callback_data": "menu_record"}],
        [{"text": "⚙️ تنظیمات", "callback_data": "menu_settings"},
         {"text": "❓ راهنما", "callback_data": "menu_help"}]
    ]
    if is_admin:
        base.append([{"text": "🛠️ پنل ادمین", "callback_data": "menu_admin"}])
    base.append([{"text": "🕸️ خزنده وحشی", "callback_data": "menu_crawler"}])
    return {"inline_keyboard": base}

def settings_keyboard(settings: UserSettings, subscription: str):
    rec = settings.record_time
    dlm = "سریع ⚡" if settings.default_download_mode == "stream" else "عادی 💾"
    mode = {"text": "📄 متن", "media": "🎬 مدیا", "explorer": "🔍 جستجوگر"}[settings.browser_mode]
    deep = "🧠 منطقی" if settings.deep_scan_mode == "logical" else "🗑 همه چیز"
    rec_behavior = "🖱️ کلیک" if settings.record_behavior == "click" else "📜 اسکرول"
    audio = "🔊 با صدا" if settings.audio_enabled else "🔇 بی‌صدا"
    vfmt = settings.video_format.upper()
    incognito = "🕶️ ناشناس" if settings.incognito_mode else "👤 عادی"
    delivery = "ZIP 📦" if settings.video_delivery == "zip" else "تکه‌ای 🧩"
    res = settings.video_resolution
    crawler = f"🕸️ خزنده: {settings.crawler_mode} | لایه: {settings.crawler_layers} | لیمیت: {'خودکار' if settings.crawler_limit == 0 else settings.crawler_limit}"

    kb = [
        [{"text": f"⏱️ زمان: {rec}m", "callback_data": "set_rec"}],
        [{"text": f"📥 دانلود: {dlm}", "callback_data": "set_dlmode"}],
        [{"text": f"🌐 حالت: {mode}", "callback_data": "set_brwmode"}],
        [{"text": f"🔍 جستجو: {deep}", "callback_data": "set_deep"}],
        [{"text": f"🎬 رفتار: {rec_behavior}", "callback_data": "set_recbeh"}],
        [{"text": audio, "callback_data": "set_audio"}],
        [{"text": f"🎞️ فرمت: {vfmt}", "callback_data": "set_vfmt"}],
        [{"text": incognito, "callback_data": "set_incognito"}],
        [{"text": f"📦 ارسال: {delivery}", "callback_data": "set_viddel"}],
        [{"text": f"📺 کیفیت: {res}", "callback_data": "set_resolution"}],
        [{"text": crawler, "callback_data": "set_crawler"}],
        [{"text": "🔙 بازگشت", "callback_data": "back_main"}]
    ]
    return {"inline_keyboard": kb}

# ═══════════════ ابزارهای فایل ═══════════════
def is_direct_file_url(url: str) -> bool:
    known_extensions = [
        '.zip','.rar','.7z','.pdf','.mp4','.mkv','.avi','.mp3',
        '.exe','.apk','.dmg','.iso','.tar','.gz','.bz2','.xz','.whl',
        '.deb','.rpm','.msi','.pkg','.appimage','.jar','.war',
        '.py','.sh','.bat','.run','.bin','.img','.mov','.flv','.wmv',
        '.webm','.ogg','.wav','.flac','.csv','.docx','.pptx','.m3u8'
    ]
    path = urlparse(url).path.lower()
    if any(path.endswith(ext) for ext in known_extensions):
        return True
    filename = path.split('/')[-1]
    if '.' in filename:
        ext = filename.rsplit('.', 1)[-1]
        if ext and re.match(r'^[a-zA-Z0-9_-]+$', ext) and len(ext) <= 10:
            return True
    return False

def get_filename_from_url(url):
    path = unquote(urlparse(url).path)
    name = os.path.basename(path)
    return name if name and '.' in name else "downloaded_file"

def crawl_for_download_link(start_url, max_depth=1, max_pages=10, timeout_seconds=30):
    visited = set()
    q = queue.Queue()
    q.put((start_url, 0))
    s = requests.Session()
    s.headers.update({"User-Agent": "Mozilla/5.0"})
    pc = 0
    start_time = time.time()
    while not q.empty():
        if time.time() - start_time > timeout_seconds:
            break
        cur, depth = q.get()
        if cur in visited or depth > max_depth or pc > max_pages:
            continue
        visited.add(cur)
        pc += 1
        try:
            r = s.get(cur, timeout=10)
        except:
            continue
        if is_direct_file_url(cur):
            return cur
        if "text/html" in r.headers.get("Content-Type", ""):
            soup = BeautifulSoup(r.text, "html.parser")
            for a in soup.find_all("a", href=True):
                href = urljoin(cur, a["href"])
                if is_direct_file_url(href):
                    return href
                if depth + 1 <= max_depth:
                    q.put((href, depth+1))
    return None

def split_file_binary(file_path, prefix, ext):
    d = os.path.dirname(file_path) or "."
    if not os.path.exists(file_path):
        return []
    parts = []
    video_exts = ('.webm', '.mkv', '.mp4', '.avi', '.mov')
    if ext.lower() in video_exts and shutil.which('ffmpeg'):
        try:
            out_pattern = os.path.join(d, f"{prefix}_part%03d{ext}")
            subprocess.run([
                'ffmpeg', '-y', '-i', file_path, '-c', 'copy', '-map', '0',
                '-f', 'segment', '-segment_size', str(ZIP_PART_SIZE),
                '-reset_timestamps', '1', out_pattern
            ], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
            parts = sorted([os.path.join(d, f) for f in os.listdir(d) if f.startswith(f"{prefix}_part") and f.endswith(ext)])
            if parts:
                return parts
        except Exception as e:
            safe_print(f"ffmpeg segment failed: {e}, falling back to binary split")
    with open(file_path, "rb") as f:
        i = 1
        while True:
            chunk = f.read(ZIP_PART_SIZE)
            if not chunk:
                break
            pname = f"{prefix}.{i:03d}{ext}" if ext.lower() != ".zip" else f"{prefix}.zip.{i:03d}"
            ppath = os.path.join(d, pname)
            with open(ppath, "wb") as pf:
                pf.write(chunk)
            parts.append(ppath)
            i += 1
    return parts

def create_zip_and_split(src, base):
    d = os.path.dirname(src) or "."
    if not os.path.exists(src):
        return []
    zp = os.path.join(d, f"{base}.zip")
    try:
        with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as zf:
            zf.write(src, os.path.basename(src))
    except:
        return []
    if os.path.getsize(zp) <= ZIP_PART_SIZE:
        return [zp]
    parts = split_file_binary(zp, base, ".zip")
    os.remove(zp)
    return parts

# ═══════════════ استخراج عناصر صفحه ═══════════════
def extract_clickable_and_media(page, mode):
    links = []
    elements = page.query_selector_all('a[href]')
    for el in elements:
        href = el.get_attribute('href')
        text = el.inner_text().strip()[:50] or href[:50]
        if not href or not href.startswith(('http://', 'https://')):
            continue
        links.append(("link", text, href))
    video_urls = []
    if mode == "media":
        for el in page.query_selector_all('video source, video[src]'):
            src = el.get_attribute('src')
            if src and src.startswith('http'):
                video_urls.append(src)
        for el in page.query_selector_all('iframe[src]'):
            src = el.get_attribute('src')
            if src and src.startswith('http'):
                video_urls.append(src)
    return links, video_urls

# ═══════════════ اسکرین‌شات ═══════════════
def screenshot_full(browser, url, out):
    page = browser.new_page()
    try:
        page.goto(url, timeout=90000, wait_until="domcontentloaded")
        page.wait_for_timeout(2000)
        page.screenshot(path=out, full_page=True)
    finally:
        page.close()

def screenshot_2x(browser, url, out):
    page = browser.new_page()
    try:
        page.goto(url, timeout=90000, wait_until="domcontentloaded")
        page.wait_for_timeout(2000)
        page.evaluate("document.body.style.zoom = '200%'")
        page.wait_for_timeout(500)
        page.screenshot(path=out, full_page=True)
    finally:
        page.close()

def screenshot_4k(browser, url, out):
    page = browser.new_page()
    try:
        page.set_viewport_size({"width": 3840, "height": 2160})
        page.goto(url, timeout=90000, wait_until="domcontentloaded")
        page.wait_for_timeout(3000)
        page.screenshot(path=out, full_page=True)
    finally:
        page.close()

# ═══════════════ صف‌ها (In-Memory با قفل) ═══════════════
def load_queue(queue_type: str) -> list:
    with queue_locks[queue_type]:
        return list(inmemory_queues[queue_type])

def save_queue(queue_type: str, data: list):
    with queue_locks[queue_type]:
        inmemory_queues[queue_type] = list(data)

def enqueue_job(job: Job, queue_type: str):
    with queue_locks[queue_type]:
        q = load_queue(queue_type)
        q.append(asdict(job))
        save_queue(queue_type, q)

def dequeue_job(queue_type: str) -> Optional[Job]:
    with queue_locks[queue_type]:
        q = load_queue(queue_type)
        for i, item in enumerate(q):
            if item["status"] == "queued":
                item["status"] = "running"
                item["updated_at"] = time.time()
                item["started_at"] = time.time()
                save_queue(queue_type, q)
                return Job(**item)
    return None

def update_job(job: Job):
    with queue_locks[job.queue_type]:
        q = load_queue(job.queue_type)
        for i, item in enumerate(q):
            if item["job_id"] == job.job_id:
                q[i] = asdict(job)
                save_queue(job.queue_type, q)
                return
        q.append(asdict(job))
        save_queue(job.queue_type, q)

def find_job(jid: str) -> Optional[Job]:
    for qt in ["browser", "download", "record"]:
        q = load_queue(qt)
        for item in q:
            if item["job_id"] == jid:
                return Job(**item)
    return None

def count_user_jobs(chat_id: int):
    count = 0
    for qt in ["browser", "download", "record"]:
        q = load_queue(qt)
        for item in q:
            if item["chat_id"] == chat_id and item["status"] in ("queued", "running"):
                count += 1
    return count

def kill_all_user_jobs(chat_id: int):
    for qt in ["browser", "download", "record"]:
        with queue_locks[qt]:
            q = load_queue(qt)
            for item in q:
                if item["chat_id"] == chat_id and item["status"] in ("queued", "running"):
                    item["status"] = "cancelled"
                    item["updated_at"] = time.time()
            save_queue(qt, q)

def kill_all_jobs():
    for qt in ["browser", "download", "record"]:
        with queue_locks[qt]:
            q = load_queue(qt)
            for item in q:
                if item["status"] in ("queued", "running"):
                    item["status"] = "cancelled"
                    item["updated_at"] = time.time()
            save_queue(qt, q)

def close_user_context(chat_id):
    kill_all_user_jobs(chat_id)
    session = get_session(chat_id)
    session.cancel_requested = True
    session.stop_requested = True
    set_session(session)

# ═══════════════ Worker ═══════════════
def worker_loop(worker_id, stop_event, worker_type):
    safe_print(f"[Worker {worker_id} ({worker_type})] start")
    while not stop_event.is_set():
        job = None
        try:
            if worker_type == "record":
                job = dequeue_job("record")
            elif worker_type == "download":
                job = dequeue_job("download")
            else:
                job = dequeue_job("browser")

            if not job:
                time.sleep(2)
                continue

            session = get_session(job.chat_id)
            if session.cancel_requested:
                job.status = "cancelled"
                update_job(job)
                session.cancel_requested = False
                set_session(session)
                continue

            def target():
                try:
                    if job.mode == "record_video":
                        handle_record_video(job)
                    elif job.mode in ("download", "blind_download", "download_execute", "download_website", "download_all_found"):
                        process_download_job(job)
                    elif job.mode == "captcha":
                        handle_captcha(job)
                    else:
                        process_browser_job(job)
                except Exception as e:
                    safe_print(f"Job {job.job_id} error: {e}")
                    traceback.print_exc()
                    job.status = "error"
                    update_job(job)

            t = threading.Thread(target=target, daemon=True)
            t.start()
            t.join(timeout=WORKER_TIMEOUT)

            if t.is_alive():
                safe_print(f"Job {job.job_id} timed out, abandoning")
                job.status = "error"
                update_job(job)
        except Exception as e:
            safe_print(f"Worker {worker_id} crashed: {e}")
            traceback.print_exc()
            time.sleep(5)

# ═══════════════ اسکن ویدیو هوشمند ═══════════════
def scan_videos_smart(page):
    elements = page.evaluate("""() => {
        const results = [];
        const centerX = window.innerWidth / 2;
        const centerY = window.innerHeight / 2;
        document.querySelectorAll('video').forEach(v => {
            const rect = v.getBoundingClientRect();
            if (rect.width < 200 || rect.height < 150) return;
            let src = v.src || (v.querySelector('source') ? v.querySelector('source').src : '');
            if (!src) return;
            const area = rect.width * rect.height;
            const dist = Math.sqrt(Math.pow(rect.x + rect.width/2 - centerX, 2) + Math.pow(rect.y + rect.height/2 - centerY, 2));
            results.push({text: 'video element', href: src, score: area - dist*2, w: rect.width, h: rect.height});
        });
        document.querySelectorAll('iframe').forEach(f => {
            const rect = f.getBoundingClientRect();
            if (rect.width < 300 || rect.height < 200) return;
            let src = f.src || '';
            if (!src.startsWith('http')) return;
            const area = rect.width * rect.height;
            const dist = Math.sqrt(Math.pow(rect.x + rect.width/2 - centerX, 2) + Math.pow(rect.y + rect.height/2 - centerY, 2));
            results.push({text: 'iframe', href: src, score: area - dist*2, w: rect.width, h: rect.height});
        });
        return results;
    }""")

    network_urls = []
    def capture(response):
        ct = response.headers.get("content-type", "")
        url = response.url.lower()
        if "mpegurl" in ct or "dash+xml" in ct or url.endswith((".m3u8", ".mpd")) or \
           ("video" in ct and (url.endswith(".mp4") or url.endswith(".webm") or url.endswith(".mkv"))):
            network_urls.append(response.url)
    page.on("response", capture)
    page.wait_for_timeout(3000)
    page.remove_listener("response", capture)

    json_urls = page.evaluate("""() => {
        const results = [];
        const scripts = document.querySelectorAll('script');
        for (const s of scripts) {
            const text = s.textContent || '';
            const matches = text.match(/(https?:\\/\\/[^"']+\\.(?:m3u8|mp4|mkv|webm|mpd)[^"']*)/gi);
            if (matches) results.push(...matches);
        }
        return results;
    }""")

    all_candidates = []
    for el in elements:
        href = el["href"]
        if not href.startswith("http"):
            continue
        parsed = urlparse(href)
        if any(ad in parsed.netloc for ad in AD_DOMAINS):
            continue
        if any(kw in href.lower() for kw in BLOCKED_AD_KEYWORDS):
            continue
        all_candidates.append({
            "text": (el["text"] + f" ({parsed.netloc})")[:35],
            "href": href,
            "score": el["score"]
        })
    for url in network_urls:
        if url in [c["href"] for c in all_candidates]:
            continue
        parsed = urlparse(url)
        if any(ad in parsed.netloc for ad in AD_DOMAINS):
            continue
        all_candidates.append({
            "text": f"Network stream ({parsed.netloc})"[:35],
            "href": url,
            "score": 100000
        })
    for url in json_urls:
        if url in [c["href"] for c in all_candidates]:
            continue
        parsed = urlparse(url)
        if any(ad in parsed.netloc for ad in AD_DOMAINS):
            continue
        all_candidates.append({
            "text": f"JSON stream ({parsed.netloc})"[:35],
            "href": url,
            "score": 90000
        })
    all_candidates.sort(key=lambda x: x["score"], reverse=True)
    return all_candidates

def smooth_scroll_to_video(page):
    coords = page.evaluate("""() => {
        let best = null; let bestArea = 0;
        document.querySelectorAll('video').forEach(v => {
            const rect = v.getBoundingClientRect();
            if (rect.width < 200 || rect.height < 150) return;
            const area = rect.width * rect.height;
            if (area > bestArea) { bestArea = area; best = { y: rect.top + window.scrollY, x: rect.left + window.scrollX, w: rect.width, h: rect.height }; }
        });
        document.querySelectorAll('iframe').forEach(f => {
            const rect = f.getBoundingClientRect();
            if (rect.width < 300 || rect.height < 200) return;
            const area = rect.width * rect.height;
            if (area > bestArea) { bestArea = area; best = { y: rect.top + window.scrollY, x: rect.left + window.scrollX, w: rect.width, h: rect.height }; }
        });
        return best || { y: window.scrollY, x: 0, w: 0, h: 0 };
    }""")
    target_y = coords["y"]
    current_y = page.evaluate("window.scrollY")
    distance = target_y - current_y
    steps = max(20, abs(distance) // 15)
    step_size = distance / steps
    for i in range(steps):
        current_y += step_size
        page.evaluate(f"window.scrollTo({{top: {int(current_y)}, behavior: 'smooth'}})")
        page.wait_for_timeout(50)
    page.evaluate(f"window.scrollTo({{top: {int(target_y)}, behavior: 'smooth'}})")
    page.wait_for_timeout(200)

def find_video_center(page):
    coords = page.evaluate("""() => {
        const centerX = window.innerWidth / 2;
        const centerY = window.innerHeight / 2;
        let best = null; let bestArea = 0;
        document.querySelectorAll('video').forEach(v => {
            const rect = v.getBoundingClientRect();
            if (rect.width < 200 || rect.height < 150) return;
            const area = rect.width * rect.height;
            if (area > bestArea) { bestArea = area; best = { x: rect.x + rect.width / 2, y: rect.y + rect.height / 2 }; }
        });
        document.querySelectorAll('iframe').forEach(f => {
            const rect = f.getBoundingClientRect();
            if (rect.width < 300 || rect.height < 200) return;
            const area = rect.width * rect.height;
            if (area > bestArea) { bestArea = area; best = { x: rect.x + rect.width / 2, y: rect.y + rect.height / 2 }; }
        });
        return best || { x: centerX, y: centerY };
    }""")
    return coords["x"], coords["y"]

# ═══════════════ ادامه در پارت دوم... ═══════════════
# (توابع اصلی پردازش Jobها، ضبط، مرورگر، کاوشگر، پیام‌ها، callbackها)


# ═══════════════ پردازش Jobهای مرورگر ═══════════════
def process_browser_job(job: Job):
    chat_id = job.chat_id
    session = get_session(chat_id)

    if job.mode == "captcha":
        handle_captcha(job)
        return
    if job.mode == "scan_videos":
        if not session.is_admin:
            err = check_rate_limit(chat_id, "scan_videos")
            if err:
                send_message(chat_id, err)
                job.status = "cancelled"; update_job(job)
                return
        handle_scan_videos(job)
        return
    if job.mode == "scan_downloads":
        if not session.is_admin:
            err = check_rate_limit(chat_id, "scan_downloads")
            if err:
                send_message(chat_id, err)
                job.status = "cancelled"; update_job(job)
                return
        handle_scan_downloads(job)
        return
    if job.mode == "extract_commands":
        if not session.is_admin:
            err = check_rate_limit(chat_id, "extract_commands")
            if err:
                send_message(chat_id, err)
                job.status = "cancelled"; update_job(job)
                return
        handle_extract_commands(job)
        return
    if job.mode == "smart_analyze":
        handle_smart_analyze(job)
        return
    if job.mode == "source_analyze":
        handle_source_analyze(job)
        return
    if job.mode == "fullpage_screenshot":
        if not session.is_admin:
            err = check_rate_limit(chat_id, "fullpage_screenshot")
            if err:
                send_message(chat_id, err)
                job.status = "cancelled"; update_job(job)
                return
        handle_fullpage_screenshot(job)
        return
    if job.mode == "interactive_scan":
        if not session.is_admin:
            err = check_rate_limit(chat_id, "interactive_scan")
            if err:
                send_message(chat_id, err)
                job.status = "cancelled"; update_job(job)
                return
        handle_interactive_scan(job)
        return
    if job.mode == "interactive_execute":
        handle_interactive_execute(job)
        return

    session.current_job_id = job.job_id
    set_session(session)
    job_dir = os.path.join("jobs_data", job.job_id)
    os.makedirs(job_dir, exist_ok=True)

    pw = sync_playwright().start()
    browser = None
    try:
        browser = pw.chromium.launch(
            headless=True,
            args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu",
                  "--disable-blink-features=AutomationControlled",
                  "--autoplay-policy=no-user-gesture-required"]
        )
        session = get_session(chat_id)
        if session.cancel_requested:
            raise InterruptedError("cancel")

        if job.mode == "screenshot":
            if not session.is_admin:
                err = check_rate_limit(chat_id, "screenshot")
                if err:
                    send_message(chat_id, err)
                    job.status = "cancelled"; update_job(job)
                    return
            send_message(chat_id, "📸 اسکرین‌شات...")
            spath = os.path.join(job_dir, "screenshot.png")
            screenshot_full(browser, job.url, spath)
            send_document(chat_id, spath, caption="✅ اسکرین‌شات")
            if session.subscription in ("طلایی", "الماسی") or session.is_admin:
                kb = {"inline_keyboard": [
                    [{"text": "🔍 2x Zoom", "callback_data": f"req2x_{job.job_id}"},
                     {"text": "🖼️ 4K", "callback_data": f"req4k_{job.job_id}"}]
                ]}
                send_message(chat_id, "کیفیت بالاتر:", reply_markup=kb)
            job.status = "done"; update_job(job)

        elif job.mode == "2x_screenshot":
            if not session.is_admin:
                err = check_rate_limit(chat_id, "2x_screenshot")
                if err:
                    send_message(chat_id, err)
                    job.status = "cancelled"; update_job(job)
                    return
            send_message(chat_id, "🔍 2x Zoom...")
            spath = os.path.join(job_dir, "screenshot_2x.png")
            screenshot_2x(browser, job.url, spath)
            send_document(chat_id, spath, caption="✅ اسکرین‌شات 2x")
            job.status = "done"; update_job(job)

        elif job.mode == "4k_screenshot":
            if not session.is_admin:
                err = check_rate_limit(chat_id, "4k_screenshot")
                if err:
                    send_message(chat_id, err)
                    job.status = "cancelled"; update_job(job)
                    return
            send_message(chat_id, "🖼️ 4K...")
            spath = os.path.join(job_dir, "screenshot_4k.png")
            screenshot_4k(browser, job.url, spath)
            send_document(chat_id, spath, caption="✅ اسکرین‌شات 4K")
            job.status = "done"; update_job(job)

        elif job.mode in ("browser", "browser_click"):
            if not session.is_admin:
                err = check_rate_limit(chat_id, "browser")
                if err:
                    send_message(chat_id, err)
                    job.status = "cancelled"; update_job(job)
                    return
            handle_browser(job, job_dir, browser)
        else:
            send_message(chat_id, "❌ نامعتبر")
            job.status = "error"; update_job(job)

    except InterruptedError:
        send_message(chat_id, "⏹️ لغو شد.")
        job.status = "cancelled"; update_job(job)
    except Exception as e:
        send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"; update_job(job)
    finally:
        if browser:
            browser.close()
        pw.stop()
        shutil.rmtree(job_dir, ignore_errors=True)
        final = find_job(job.job_id)
        if final and final.status in ("done","error","cancelled"):
            s = get_session(chat_id)
            if s.state != "browsing":
                s.state = "idle"
                s.current_job_id = None
                s.cancel_requested = False
                set_session(s)
                send_message(chat_id, "🔄 آماده.", reply_markup=main_menu_keyboard(s.is_admin))

# ═══════════════ پردازش Jobهای دانلود ═══════════════
def process_download_job(job: Job):
    chat_id = job.chat_id
    session = get_session(chat_id)

    if job.mode == "download_execute":
        job_dir = os.path.join("jobs_data", job.job_id)
        os.makedirs(job_dir, exist_ok=True)
        try:
            execute_download(job, job_dir)
        except Exception as e:
            send_message(chat_id, f"❌ خطا: {e}")
            job.status = "error"; update_job(job)
        finally:
            shutil.rmtree(job_dir, ignore_errors=True)
        return

    if job.mode == "download_website":
        if not session.is_admin:
            err = check_rate_limit(chat_id, "download_website")
            if err:
                send_message(chat_id, err)
                job.status = "cancelled"; update_job(job)
                return
        download_full_website(job)
        return
    if job.mode == "blind_download":
        handle_blind_download(job)
        return
    if job.mode == "download_all_found":
        handle_download_all_found(job)
        return

    job_dir = os.path.join("jobs_data", job.job_id)
    os.makedirs(job_dir, exist_ok=True)
    try:
        if job.mode == "download":
            handle_download(job, job_dir)
        else:
            send_message(chat_id, "❌ نامعتبر")
            job.status = "error"; update_job(job)
    except Exception as e:
        send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"; update_job(job)
    finally:
        shutil.rmtree(job_dir, ignore_errors=True)

# ═══════════════ دانلود هوشمند ═══════════════
def handle_download(job, job_dir):
    chat_id = job.chat_id; session = get_session(chat_id)
    url = job.url
    if is_direct_file_url(url):
        direct_link = url
    else:
        send_message(chat_id, "🔎 جستجوی فایل...")
        direct_link = crawl_for_download_link(url)
        if not direct_link:
            send_message(chat_id, "⚠️ دانلود کور...")
            job.mode = "blind_download"; job.url = url; job.queue_type = "download"
            update_job(job)
            handle_blind_download(job)
            return

    size_bytes = None; size_str = "نامشخص"
    try:
        head = requests.head(direct_link, timeout=10, allow_redirects=True)
        if head.headers.get("Content-Length"):
            size_bytes = int(head.headers["Content-Length"])
            size_str = f"{size_bytes/(1024*1024):.2f} MB"
    except: pass

    if not session.is_admin:
        err = check_rate_limit(chat_id, "download", size_bytes)
        if err:
            send_message(chat_id, err)
            job.status = "cancelled"; update_job(job)
            return

    fname = get_filename_from_url(direct_link)
    kb = {"inline_keyboard": [
        [{"text": "📦 ZIP", "callback_data": f"dlzip_{job.job_id}"},
         {"text": "📄 اصلی", "callback_data": f"dlraw_{job.job_id}"}],
        [{"text": "❌ لغو", "callback_data": f"canceljob_{job.job_id}"}]
    ]}
    send_message(chat_id, f"📄 {fname} ({size_str})", reply_markup=kb)
    job.status = "awaiting_user"
    job.extra = {"direct_link": direct_link, "filename": fname}
    update_job(job)

def download_and_stream(url, fname, job_dir, chat_id):
    base, ext = os.path.splitext(fname)
    buf = b""; idx = 1
    with requests.get(url, stream=True, timeout=120, headers={"User-Agent":"Mozilla/5.0"}) as r:
        for chunk in r.iter_content(chunk_size=8192):
            buf += chunk
            while len(buf) >= ZIP_PART_SIZE:
                session = get_session(chat_id)
                if session.cancel_requested:
                    return
                part = buf[:ZIP_PART_SIZE]; buf = buf[ZIP_PART_SIZE:]
                pname = f"{base}.part{idx:03d}{ext}"
                ppath = os.path.join(job_dir, pname)
                with open(ppath, "wb") as f: f.write(part)
                send_document(chat_id, ppath, caption=f"⚡ پارت {idx}")
                os.remove(ppath); idx += 1
        if buf:
            session = get_session(chat_id)
            if not session.cancel_requested:
                pname = f"{base}.part{idx:03d}{ext}"; ppath = os.path.join(job_dir, pname)
                with open(ppath, "wb") as f: f.write(buf)
                send_document(chat_id, ppath, caption=f"⚡ پارت {idx}")
                os.remove(ppath)

def execute_download(job, job_dir):
    chat_id = job.chat_id; extra = job.extra
    session = get_session(chat_id)
    mode = session.settings.default_download_mode
    pack_zip = extra.get("pack_zip", False)
    if mode == "stream" and pack_zip:
        send_message(chat_id, "📦 ZIP با حالت سریع ممکن نیست؛ دانلود عادی انجام می‌شود.")
        mode = "store"
    if mode == "stream":
        send_message(chat_id, "⚡ دانلود همزمان...")
        download_and_stream(extra["direct_link"], extra["filename"], job_dir, chat_id)
        job.status = "done"; update_job(job)
        return
    fname = extra["filename"]
    if "file_path" in extra:
        fpath = extra["file_path"]
    else:
        fpath = os.path.join(job_dir, fname)
        send_message(chat_id, "⏳ دانلود...")
        with requests.get(extra["direct_link"], stream=True, timeout=120, headers={"User-Agent":"Mozilla/5.0"}) as r:
            with open(fpath, "wb") as f:
                for c in r.iter_content(8192):
                    if get_session(chat_id).cancel_requested:
                        f.close()
                        os.remove(fpath)
                        return
                    f.write(c)
    if not os.path.exists(fpath):
        send_message(chat_id, "❌ فایل یافت نشد."); job.status = "error"; update_job(job); return
    if pack_zip:
        parts = create_zip_and_split(fpath, fname); label = "ZIP"
    else:
        base, ext = os.path.splitext(fname)
        parts = split_file_binary(fpath, base, ext); label = "اصلی"
    if not parts:
        send_message(chat_id, "❌ خطا در تقسیم فایل."); job.status = "error"; update_job(job); return
    instr = os.path.join(job_dir, "merge.txt")
    with open(instr, "w") as f:
        if pack_zip:
            f.write("همه‌ی فایل‌ها را دانلود کنید، سپس فایل .001 را با WinRAR یا 7-Zip باز کنید.")
        else:
            f.write(f"هر قطعه به‌طور مستقل قابل پخش است. برای ادغام: copy /b {'+'.join([os.path.basename(p) for p in parts])} {fname}")
    send_document(chat_id, instr, caption="📝 راهنما")
    for idx, p in enumerate(parts, 1):
        if get_session(chat_id).cancel_requested:
            break
        send_document(chat_id, p, caption=f"{label} پارت {idx}/{len(parts)}")
    job.status = "done"; update_job(job)

def handle_blind_download(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    url = job.url
    job_dir = os.path.join("jobs_data", job.job_id)
    os.makedirs(job_dir, exist_ok=True)
    send_message(chat_id, "⏳ دانلود اولیه...")
    try:
        with requests.get(url, stream=True, timeout=120, headers={"User-Agent":"Mozilla/5.0"}) as r:
            ct = r.headers.get("Content-Type", "application/octet-stream")
            fname = get_filename_from_url(url)
            if '.' not in fname:
                if "video" in ct: fname += ".mp4"
                elif "pdf" in ct: fname += ".pdf"
                else: fname += ".bin"
            fpath = os.path.join(job_dir, fname)
            with open(fpath, "wb") as f:
                for c in r.iter_content(8192):
                    if get_session(chat_id).cancel_requested:
                        f.close()
                        os.remove(fpath)
                        return
                    f.write(c)
        if not os.path.exists(fpath):
            send_message(chat_id, "❌ فایل دانلود نشد."); job.status = "error"; update_job(job); return
        size_bytes = os.path.getsize(fpath); size_str = f"{size_bytes/(1024*1024):.2f} MB"
        if not session.is_admin:
            err = check_rate_limit(chat_id, "download", size_bytes)
            if err:
                send_message(chat_id, err)
                job.status = "cancelled"; update_job(job)
                return
        text = f"📄 فایل (کور): {fname} ({size_str})"
        kb = {"inline_keyboard": [
            [{"text":"📦 ZIP","callback_data":f"dlblindzip_{job.job_id}"},
             {"text":"📄 اصلی","callback_data":f"dlblindra_{job.job_id}"}],
            [{"text":"❌ لغو","callback_data":f"canceljob_{job.job_id}"}]
        ]}
        send_message(chat_id, text, reply_markup=kb)
        job.status = "awaiting_user"
        job.extra = {"file_path": fpath, "filename": fname}
        update_job(job)
    except Exception as e:
        send_message(chat_id, f"❌ دانلود کور ناموفق: {e}")
        job.status = "error"; update_job(job)
        shutil.rmtree(job_dir, ignore_errors=True)

# ═══════════════ دانلود کامل وب‌سایت ═══════════════
def download_full_website(job):
    chat_id = job.chat_id; url = job.url
    job_dir = os.path.join("jobs_data", job.job_id)
    os.makedirs(job_dir, exist_ok=True)
    send_message(chat_id, "🌐 دانلود کامل وب‌سایت...")
    if shutil.which("wget"):
        try:
            ua = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"
            cmd = ["wget", "--adjust-extension", "--span-hosts", "--convert-links",
                   "--page-requisites", "--no-directories", "--directory-prefix", job_dir,
                   "--recursive", "--level=1", "--accept", "html,css,js,jpg,jpeg,png,gif,svg,mp4,webm,pdf",
                   "--user-agent", ua, "--header", "Accept: */*", "--timeout", "30", "--tries", "2", url]
            if subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300).returncode == 0:
                _finish_website_download(job, job_dir)
                return
        except: pass
    send_message(chat_id, "🔄 دانلود با مرورگر مخفی...")
    pw = sync_playwright().start(); browser = None
    try:
        browser = pw.chromium.launch(headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
        page = browser.new_page()
        page.goto(url, timeout=60000, wait_until="domcontentloaded")
        page.wait_for_timeout(3000)
        html = page.content()
        with open(os.path.join(job_dir, "index.html"), "w", encoding="utf-8") as f: f.write(html)
        page.screenshot(path=os.path.join(job_dir, "screenshot.png"), full_page=True)
        page.close()
        _finish_website_download(job, job_dir)
    except Exception as e:
        send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"; update_job(job)
        shutil.rmtree(job_dir, ignore_errors=True)
    finally:
        if browser: browser.close()
        pw.stop()

def _finish_website_download(job, job_dir):
    chat_id = job.chat_id
    all_files = []
    for root, _, files in os.walk(job_dir):
        for f in files: all_files.append(os.path.join(root, f))
    if not all_files:
        send_message(chat_id, "❌ محتوایی یافت نشد.")
        job.status = "error"; update_job(job); return
    zp = os.path.join(job_dir, "website.zip")
    with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as zf:
        for fp in all_files: zf.write(fp, os.path.relpath(fp, job_dir))
    parts = split_file_binary(zp, "website", ".zip") if os.path.getsize(zp) > ZIP_PART_SIZE else [zp]
    instr = os.path.join(job_dir, "merge.txt")
    with open(instr, "w") as f: f.write("همه‌ی فایل‌ها را دانلود کنید، سپس فایل .001 را با WinRAR یا 7-Zip باز کنید.")
    send_document(chat_id, instr, caption="📝 راهنما")
    for idx, p in enumerate(parts, 1):
        send_document(chat_id, p, caption=f"🌐 پارت {idx}/{len(parts)}")
    job.status = "done"; update_job(job)
    shutil.rmtree(job_dir, ignore_errors=True)

# ═══════════════ ضبط ویدیو (بدون Live) ═══════════════
def get_firefox_browser():
    pw = sync_playwright().start()
    browser = pw.firefox.launch(
        headless=True,
        firefox_user_prefs={
            "media.autoplay.default": 0,
            "media.autoplay.enabled": True,
            "media.volume_scale": "1.0",
        },
        args=['--no-sandbox']
    )
    return pw, browser

def handle_record_video(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    url = job.url
    rec_time_minutes = session.settings.record_time
    rec_time_seconds = rec_time_minutes * 60
    behavior = session.settings.record_behavior   # "click" یا "scroll"
    video_format = session.settings.video_format
    delivery = session.settings.video_delivery
    resolution = session.settings.video_resolution
    audio_enabled = session.settings.audio_enabled

    MAX_REC_MINUTES = MAX_RECORD_MINUTES_ADMIN if session.is_admin else MAX_RECORD_MINUTES_USER
    MAX_REC_SECONDS = MAX_REC_MINUTES * 60

    if rec_time_seconds > MAX_REC_SECONDS:
        send_message(chat_id, f"⛔ حداکثر زمان ضبط {MAX_REC_MINUTES} دقیقه می‌باشد.")
        job.status = "cancelled"; update_job(job); return

    res_req = RES_REQUIREMENTS.get(resolution, [])
    if session.subscription not in res_req and not session.is_admin:
        send_message(chat_id, f"⛔ کیفیت {resolution} برای سطح «{session.subscription}» در دسترس نیست.")
        job.status = "cancelled"; update_job(job); return

    if resolution == "4k" and not session.is_admin:
        if rec_time_seconds > MAX_4K_RECORD_MINUTES * 60:
            send_message(chat_id, f"⛔ حداکثر زمان ضبط 4K برابر {MAX_4K_RECORD_MINUTES} دقیقه است.")
            job.status = "cancelled"; update_job(job); return

    w, h = ALLOWED_RESOLUTIONS.get(resolution, (1280, 720))
    job_dir = os.path.join("jobs_data", job.job_id)
    os.makedirs(job_dir, exist_ok=True)

    send_message(chat_id, f"🎬 ضبط {rec_time_minutes} دقیقه ({'اسکرول' if behavior == 'scroll' else 'کلیک'}) با کیفیت {resolution}...")

    if os.environ.get("CI") or os.environ.get("GITHUB_ACTIONS"):
        audio_enabled = False

    _rec_pw = None; _rec_browser = None
    audio_proc = None; audio_path = None
    try:
        _rec_pw, _rec_browser = get_firefox_browser()
        context = _rec_browser.new_context(
            viewport={"width": w, "height": h},
            record_video_dir=job_dir,
            record_video_size={"width": w, "height": h}
        )
        page = context.new_page()

        try:
            page.goto(url, timeout=60000, wait_until="domcontentloaded")
            page.wait_for_timeout(2000)
            if behavior == "scroll":
                smooth_scroll_to_video(page)
            vx, vy = find_video_center(page)
            page.mouse.click(vx, vy)
            try: page.evaluate("() => { const v = document.querySelector('video'); if (v) v.play(); }")
            except: pass

            if audio_enabled:
                try:
                    subprocess.run(["pactl", "load-module", "module-null-sink", "sink_name=virtual_out"], check=False)
                    time.sleep(1)
                    sink_input = subprocess.run(
                        "pactl list sink-inputs | grep -B 18 -i 'firefox' | grep 'Sink Input' | awk '{print $3}' | cut -d '#' -f 2",
                        shell=True, capture_output=True, text=True
                    ).stdout.strip()
                    if sink_input:
                        subprocess.run(["pactl", "move-sink-input", sink_input, "virtual_out"], check=False)
                    audio_path = os.path.join(job_dir, "audio.mp3")
                    audio_proc = subprocess.Popen(
                        ['ffmpeg', '-y', '-f', 'pulse', '-i', 'virtual_out.monitor',
                         '-ac', '2', '-ar', '44100', '-acodec', 'libmp3lame', '-b:a', '128k', audio_path],
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE
                    )
                except Exception as e:
                    safe_print(f"Audio setup failed: {e}")

            start_time = time.time()
            while time.time() - start_time < rec_time_seconds:
                if get_session(chat_id).cancel_requested:
                    send_message(chat_id, "⏹️ ضبط متوقف شد.")
                    break
                time.sleep(0.5)

        finally:
            page.close()
            context.close()

        if audio_proc:
            try:
                audio_proc.terminate()
                audio_proc.wait(timeout=5)
            except: pass

        webm = None
        for f in os.listdir(job_dir):
            if f.endswith('.webm'):
                webm = os.path.join(job_dir, f)
                break
        if not webm:
            send_message(chat_id, "❌ ویدیویی ضبط نشد.")
            job.status = "error"; update_job(job); return

        final_video_path = webm
        if video_format != "webm":
            converted = os.path.join(job_dir, f"record.{video_format}")
            if video_format == "mp4":
                cmd = ['ffmpeg', '-y', '-i', webm, '-c:v', 'libx264', '-c:a', 'aac', '-b:a', '128k', converted]
            else:
                cmd = ['ffmpeg', '-y', '-i', webm, '-c', 'copy', converted]
            try:
                subprocess.run(cmd, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
                if os.path.exists(converted) and os.path.getsize(converted) > 0:
                    final_video_path = converted
                    os.remove(webm)
            except:
                safe_print("Video format conversion failed, keeping webm")

        def send_file(path, label_prefix, as_zip=False):
            fname = os.path.basename(path)
            if as_zip:
                if os.path.getsize(path) <= ZIP_PART_SIZE:
                    zp = os.path.join(job_dir, f"{fname}.zip")
                    with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as zf:
                        zf.write(path, fname)
                    send_document(chat_id, zp, caption=f"{label_prefix} (ZIP)")
                    os.remove(zp)
                else:
                    parts = create_zip_and_split(path, fname)
                    for idx, p in enumerate(parts, 1):
                        send_document(chat_id, p, caption=f"{label_prefix} (ZIP) پارت {idx}/{len(parts)}")
            else:
                base, ext = os.path.splitext(fname)
                if os.path.getsize(path) <= ZIP_PART_SIZE:
                    send_document(chat_id, path, caption=f"{label_prefix} (اصلی)")
                else:
                    parts = split_file_binary(path, base, ext)
                    for idx, p in enumerate(parts, 1):
                        send_document(chat_id, p, caption=f"{label_prefix} (اصلی) پارت {idx}/{len(parts)}")

        use_zip = (delivery == "zip")
        send_file(final_video_path, "🎬 ویدیو", use_zip)

        if audio_path and os.path.exists(audio_path) and os.path.getsize(audio_path) > 0:
            send_file(audio_path, "🎵 صوت", use_zip)

        job.status = "done"; update_job(job)

    except Exception as e:
        send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"; update_job(job)
        shutil.rmtree(job_dir, ignore_errors=True)
    finally:
        if _rec_browser:
            try: _rec_browser.close()
            except: pass
        if _rec_pw:
            try: _rec_pw.stop()
            except: pass

# ═══════════════ مرورگر تعاملی ═══════════════
def handle_browser(job, job_dir, browser):
    chat_id = job.chat_id; session = get_session(chat_id)
    url = job.url

    if is_direct_file_url(url):
        send_message(chat_id, "📥 این لینک یک فایل قابل دانلود است. لطفاً از بخش دانلود استفاده کنید.")
        job.status = "cancelled"; update_job(job)
        return

    mode = session.settings.browser_mode
    page = browser.new_page()

    parsed_url = urlparse(url)
    if parsed_url.netloc.lower() in (session.ad_blocked_domains or []):
        page.route("**/*", lambda route: route.abort()
                   if any(ad in route.request.url for ad in AD_DOMAINS)
                   else route.continue_())

    try:
        page.goto(url, timeout=60000, wait_until="domcontentloaded")
        page.wait_for_timeout(2000)
        spath = os.path.join(job_dir, "browser.png")
        page.screenshot(path=spath, full_page=True)
        links, video_urls = extract_clickable_and_media(page, mode)

        all_links = []
        direct_links_found = []
        for typ, text, href in links:
            all_links.append({"type": typ, "text": text[:25], "href": href})
            if is_direct_file_url(href):
                direct_links_found.append(href)
        if mode == "media":
            clean_videos = [v for v in video_urls if not any(ad in v for ad in AD_DOMAINS)]
            for vurl in clean_videos:
                all_links.append({"type": "video", "text": "🎬 ویدیو", "href": vurl})
                if is_direct_file_url(vurl):
                    direct_links_found.append(vurl)

        session.state = "browsing"
        session.browser_url = url
        session.browser_links = all_links
        session.browser_page = 0
        session.last_browser_time = time.time()
        set_session(session)

        if direct_links_found:
            for dlink in direct_links_found[:5]:
                cmd = f"/heuhshs_{hashlib.md5(dlink.encode()).hexdigest()[:6]}"
                session.text_links = session.text_links or {}
                session.text_links[cmd] = dlink
                set_session(session)
                send_message(chat_id, f"🔗 لینک دانلود مستقیم پیدا شد:\n`{dlink}`\nبرای دانلود دستور /heuhshs را بفرستید.")

        send_browser_page(chat_id, spath, url, 0)
        job.status = "done"; update_job(job)
    finally:
        page.close()

def send_browser_page(chat_id, image_path=None, url="", page_num=0):
    session = get_session(chat_id)
    all_links = session.browser_links or []
    per_page = 10
    start = page_num * per_page; end = min(start + per_page, len(all_links))
    page_links = all_links[start:end]

    keyboard_rows = []; idx = start; row = []
    for link in page_links:
        label = link["text"][:20]
        cb = f"nav_{chat_id}_{idx}" if link["type"] != "video" else f"dlvid_{chat_id}_{idx}"
        with callback_map_lock:
            callback_map[cb] = link["href"]
        row.append({"text": label, "callback_data": cb})
        if len(row) == 2: keyboard_rows.append(row); row = []
        idx += 1
    if row: keyboard_rows.append(row)

    nav = []
    if page_num > 0: nav.append({"text": "◀️", "callback_data": f"bpg_{chat_id}_{page_num-1}"})
    if end < len(all_links): nav.append({"text": "▶️", "callback_data": f"bpg_{chat_id}_{page_num+1}"})
    if nav: keyboard_rows.append(nav)

    sub = session.subscription; mode = session.settings.browser_mode
    if mode == "media":
        if sub in ("طلایی", "الماسی") or session.is_admin:
            keyboard_rows.append([{"text": "🎬 اسکن ویدیوها", "callback_data": f"scvid_{chat_id}"}])
        parsed_url = urlparse(url)
        current_domain = parsed_url.netloc.lower()
        is_blocked = current_domain in (session.ad_blocked_domains or [])
        ad_text = "🛡️ تبلیغات: روشن" if is_blocked else "🛡️ تبلیغات: خاموش"
        keyboard_rows.append([{"text": ad_text, "callback_data": f"adblock_{chat_id}"}])
    elif mode == "explorer":
        if sub in ("طلایی", "الماسی") or session.is_admin:
            keyboard_rows.append([{"text": "🔍 تحلیل هوشمند", "callback_data": f"sman_{chat_id}"}])
            keyboard_rows.append([{"text": "🕵️ تحلیل سورس", "callback_data": f"srcan_{chat_id}"}])
    else:
        if sub in ("طلایی", "الماسی") or session.is_admin:
            keyboard_rows.append([{"text": "📦 جستجوی فایل‌ها", "callback_data": f"scdl_{chat_id}"}])

    keyboard_rows.append([{"text": "🪟 حل کپچا", "callback_data": f"captcha_{chat_id}"}])

    if sub in ("طلایی", "الماسی") or session.is_admin:
        keyboard_rows.append([{"text": "📋 فرامین", "callback_data": f"extcmd_{chat_id}"}])
        keyboard_rows.append([{"text": "🎬 ضبط", "callback_data": f"recvid_{chat_id}"}])
        keyboard_rows.append([{"text": "📸 شات کامل", "callback_data": f"fullshot_{chat_id}"}])
        keyboard_rows.append([{"text": "🔎 کاوشگر", "callback_data": f"intscan_{chat_id}"}])
    if sub in ("الماسی") or session.is_admin:
        keyboard_rows.append([{"text": "🌐 دانلود سایت", "callback_data": f"dlweb_{chat_id}"}])
    keyboard_rows.append([{"text": "❌ بستن", "callback_data": f"closebrowser_{chat_id}"}])

    kb = {"inline_keyboard": keyboard_rows}
    if image_path:
        send_document(chat_id, image_path, caption=f"🌐 {url}")
    send_message(chat_id, f"صفحه {page_num+1}/{math.ceil(len(all_links)/per_page)}", reply_markup=kb)

    extra = all_links[end:]
    if extra:
        cmds = {}; lines = ["🔹 لینک‌های بیشتر:"]
        for i, link in enumerate(extra):
            cmd = f"/a{hashlib.md5(link['href'].encode()).hexdigest()[:5]}"
            cmds[cmd] = link['href']; lines.append(f"{cmd} : {link['text']}")
        send_message(chat_id, "\n".join(lines))
        existing = session.text_links or {}
        session.text_links = {**existing, **cmds}
        set_session(session)

# ═══════════════ کپچا ═══════════════
def handle_captcha(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    url = session.browser_url
    if not url:
        send_message(chat_id, "❌ مرورگری باز نیست.")
        return
    pw = sync_playwright().start(); browser = None
    try:
        browser = pw.chromium.launch(headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
        page = browser.new_page()
        page.goto(url, timeout=30000, wait_until="domcontentloaded")
        page.wait_for_timeout(2000)
        candidates = page.query_selector_all("button, input[type=submit], a[href*='download'], a[href*='file']")
        for btn in candidates[:5]:
            try:
                btn.click()
                break
            except: pass
        network_urls = []
        def on_response(response):
            if is_direct_file_url(response.url):
                network_urls.append(response.url)
        page.on("response", on_response)
        page.wait_for_timeout(15000)
        page.remove_listener("response", on_response)
        page.close()
        if network_urls:
            send_message(chat_id, "✅ لینک‌های دانلود:\n" + "\n".join(network_urls[:5]))
        else:
            send_message(chat_id, "🚫 لینک دانلودی یافت نشد.")
    except Exception as e:
        send_message(chat_id, f"❌ خطا: {e}")
    finally:
        if browser: browser.close()
        pw.stop()

# ═══════════════ توابع اسکن و تحلیل ═══════════════
def handle_scan_videos(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    pw = sync_playwright().start(); browser = None
    try:
        browser = pw.chromium.launch(headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
        page = browser.new_page()
        page.goto(session.browser_url, timeout=60000, wait_until="domcontentloaded")
        page.wait_for_timeout(3000)
        videos = scan_videos_smart(page)
        page.close()
        if not videos:
            send_message(chat_id, "🚫 هیچ ویدیویی یافت نشد.")
            job.status = "done"; update_job(job); return
        lines = [f"🎬 **{len(videos)} ویدیو یافت شد:**"]
        cmds = {}
        for i, vid in enumerate(videos[:15]):
            cmd = f"/o{hashlib.md5(vid['href'].encode()).hexdigest()[:5]}"
            cmds[cmd] = vid['href']; lines.append(f"{i+1}. {vid['text']}"); lines.append(f"   📥 {cmd}")
        send_message(chat_id, "\n".join(lines))
        session.text_links = {**(session.text_links or {}), **cmds}; set_session(session)
        job.status = "done"; update_job(job)
    except Exception as e:
        send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"; update_job(job)
    finally:
        if browser: browser.close()
        pw.stop()

def handle_smart_analyze(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    all_links = session.browser_links or []
    if not all_links:
        send_message(chat_id, "🚫 لینکی برای تحلیل وجود ندارد.")
        job.status = "done"; update_job(job); return
    videos = [l for l in all_links if is_direct_file_url(l["href"]) and any(l["href"].lower().endswith(e) for e in ('.mp4','.webm','.mkv','.m3u8','.mpd','.mov','.avi'))]
    files = [l for l in all_links if is_direct_file_url(l["href"]) and l not in videos]
    pages = [l for l in all_links if l not in videos and l not in files]
    cmds = {}
    def send_category(title, items, prefix):
        if not items: return
        lines = [f"**{title} ({len(items)}):**"]
        for i, item in enumerate(items):
            cmd = f"/{prefix}{hashlib.md5(item['href'].encode()).hexdigest()[:5]}"
            cmds[cmd] = item['href']
            lines.append(f"{cmd} : {item['text'][:40]}\n🔗 {item['href'][:80]}")
        send_message(chat_id, "\n".join(lines))
    send_category("🎬 ویدیوها", videos, "H")
    send_category("📦 فایل‌ها", files, "H")
    send_category("📄 صفحات", pages[:20], "H")
    if pages[20:]:
        lines = ["🔹 **بقیه صفحات:**"]
        for item in pages[20:]:
            cmd = f"/H{hashlib.md5(item['href'].encode()).hexdigest()[:5]}"
            cmds[cmd] = item['href']; lines.append(f"{cmd} : {item['text'][:40]}")
        send_message(chat_id, "\n".join(lines))
    session.text_links = {**(session.text_links or {}), **cmds}
    set_session(session)
    job.status = "done"; update_job(job)

def handle_source_analyze(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    pw = sync_playwright().start(); browser = None
    try:
        browser = pw.chromium.launch(headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
        page = browser.new_page()
        page.goto(session.browser_url, timeout=60000, wait_until="domcontentloaded")
        page.wait_for_timeout(2000)
        html = page.content()
        page.close()
        soup = BeautifulSoup(html, "html.parser")
        found_urls = set()
        for tag in soup.find_all(["a", "link", "script", "img", "iframe", "source", "video", "audio"]):
            for attr in ("href", "src", "data-url", "data-href", "data-link"):
                val = tag.get(attr)
                if val:
                    try: found_urls.add(urljoin(session.browser_url, val))
                    except: pass
        for script in soup.find_all("script"):
            if script.string:
                matches = re.findall(r'https?://[^\s"\'<>]+', script.string)
                for m in matches: found_urls.add(m)
        clean_urls = [u for u in found_urls if not any(ad in u for ad in AD_DOMAINS) and not any(kw in u.lower() for kw in BLOCKED_AD_KEYWORDS)]
        if not clean_urls:
            send_message(chat_id, "🚫 هیچ لینک مخفی یافت نشد.")
            job.status = "done"; update_job(job); return
        cmds = {}; lines = [f"🕵️ **{len(clean_urls)} لینک از سورس استخراج شد:**"]
        for i, url in enumerate(clean_urls[:30]):
            cmd = f"/H{hashlib.md5(url.encode()).hexdigest()[:5]}"
            cmds[cmd] = url
            label = urlparse(url).path.split("/")[-1][:30] or url[:40]
            lines.append(f"{cmd} : {label}\n🔗 {url[:80]}")
        send_message(chat_id, "\n".join(lines))
        session.text_links = {**(session.text_links or {}), **cmds}; set_session(session)
        job.status = "done"; update_job(job)
    except Exception as e:
        send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"; update_job(job)
    finally:
        if browser: browser.close()
        pw.stop()

def handle_scan_downloads(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    url = session.browser_url
    if not url:
        send_message(chat_id, "❌ صفحه‌ای برای جستجو باز نیست."); return
    deep_mode = session.settings.deep_scan_mode
    send_message(chat_id, f"🔎 جستجوی فایل‌ها ({deep_mode})...")
    found_links = set(); all_results = []
    def add_result(link):
        if link in found_links: return
        found_links.add(link)
        fname = get_filename_from_url(link); size_str = "نامشخص"; size_bytes = None
        try:
            head = requests.head(link, timeout=5, allow_redirects=True)
            if head.headers.get("Content-Length"):
                size_bytes = int(head.headers["Content-Length"])
                size_str = f"{size_bytes/1024/1024:.2f} MB"
            cd = head.headers.get("Content-Disposition", "")
            if "attachment" in cd:
                import re as _re
                fname_match = _re.findall(r'filename[^;=\n]*=["\']?([^"\';\\n]*)', cd)
                if fname_match:
                    fname = fname_match[0].strip() or fname
        except: pass
        if deep_mode == "logical" and not is_direct_file_url(link): return
        all_results.append({"name": fname[:35], "url": link, "size": size_str})

    start_time = time.time()
    pw = sync_playwright().start(); browser = None
    try:
        browser = pw.chromium.launch(headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
        page = browser.new_page()
        page.goto(url, timeout=30000, wait_until="domcontentloaded")
        page.wait_for_timeout(1000)
        all_hrefs = page.evaluate("""() => {
            return Array.from(document.querySelectorAll('a[href]'))
                        .map(a => a.href).filter(h => h.startsWith('http'));
        }""")
        page.close()
        for href in all_hrefs:
            parsed = urlparse(href)
            if any(ad in parsed.netloc for ad in AD_DOMAINS): continue
            if any(kw in href.lower() for kw in BLOCKED_AD_KEYWORDS): continue
            if is_direct_file_url(href): add_result(href)
        elapsed = time.time() - start_time
        if all_results: send_message(chat_id, f"✅ مرحله ۱: {len(all_results)} فایل ({elapsed:.1f}s)")
    except Exception as e: safe_print(f"scan_downloads stage1 error: {e}")
    finally:
        if browser: browser.close()
        pw.stop()

    if not all_results and time.time() - start_time < 60:
        send_message(chat_id, "🔄 مرحله ۲: کراول سبک...")
        try:
            s = requests.Session(); s.headers.update({"User-Agent": "Mozilla/5.0"})
            resp = s.get(url, timeout=10)
            if resp.status_code == 200 and "text/html" in resp.headers.get("Content-Type", ""):
                soup = BeautifulSoup(resp.text, "html.parser")
                links_to_crawl = []
                for a in soup.find_all("a", href=True):
                    href = urljoin(url, a["href"])
                    parsed = urlparse(href)
                    if any(ad in parsed.netloc for ad in AD_DOMAINS): continue
                    if any(kw in href.lower() for kw in BLOCKED_AD_KEYWORDS): continue
                    if is_direct_file_url(href): add_result(href)
                    else: links_to_crawl.append(href)
                for link in links_to_crawl[:15]:
                    if time.time() - start_time > 60: break
                    found = crawl_for_download_link(link, max_depth=1, max_pages=5, timeout_seconds=10)
                    if found: add_result(found)
                elapsed = time.time() - start_time
                send_message(chat_id, f"✅ مرحله ۲: مجموعاً {len(all_results)} فایل ({elapsed:.1f}s)")
        except Exception as e: safe_print(f"scan_downloads stage2 error: {e}")

    if not all_results:
        send_message(chat_id, "🚫 هیچ فایل قابل دانلودی یافت نشد.")
        job.status = "done"; update_job(job); return

    session.found_downloads = all_results; session.found_downloads_page = 0
    set_session(session)
    send_found_downloads_page(chat_id, 0)
    job.status = "done"; update_job(job)

def send_found_downloads_page(chat_id, page_num=0):
    session = get_session(chat_id)
    all_results = session.found_downloads or []
    per_page = 10; start = page_num * per_page; end = min(start + per_page, len(all_results))
    page_results = all_results[start:end]

    lines = [f"📦 **فایل‌های یافت‌شده (صفحه {page_num+1}/{math.ceil(len(all_results)/per_page)}):**"]
    cmds = {}
    for i, f in enumerate(page_results):
        idx = start + i
        cmd = f"/d{hashlib.md5(f['url'].encode()).hexdigest()[:5]}"
        cmds[cmd] = f['url']
        lines.append(f"{idx+1}. {f['name']} ({f['size']})")
        lines.append(f"   📥 {cmd}    🔗 {f['url'][:60]}")

    keyboard_rows = []; nav = []
    if page_num > 0: nav.append({"text": "◀️ قبلی", "callback_data": f"dfpg_{chat_id}_{page_num-1}"})
    if end < len(all_results): nav.append({"text": "بعدی ▶️", "callback_data": f"dfpg_{chat_id}_{page_num+1}"})
    if nav: keyboard_rows.append(nav)
    keyboard_rows.append([{"text": "📦 دانلود همه (ZIP)", "callback_data": f"dlall_{chat_id}"}])
    keyboard_rows.append([{"text": "❌ بستن", "callback_data": "close_downloads"}])

    send_message(chat_id, "\n".join(lines), reply_markup={"inline_keyboard": keyboard_rows})
    merged = {**(session.text_links or {}), **cmds}; session.text_links = merged; set_session(session)

def handle_extract_commands(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    all_links = session.browser_links or []
    if not all_links:
        send_message(chat_id, "🚫 لینکی برای استخراج وجود ندارد.")
        job.status = "done"; update_job(job); return
    cmds = {}; lines = [f"📋 **{len(all_links)} فرمان استخراج شد:**"]
    for i, link in enumerate(all_links):
        cmd = f"/H{hashlib.md5(link['href'].encode()).hexdigest()[:5]}"
        cmds[cmd] = link['href']
        line = f"{cmd} : {link['text'][:40]}\n🔗 {link['href'][:80]}"
        lines.append(line)
        if (i + 1) % 15 == 0 or i == len(all_links) - 1:
            send_message(chat_id, "\n".join(lines))
            lines = [f"📋 **ادامه فرامین ({i+1}/{len(all_links)}):**"]
    session.text_links = {**(session.text_links or {}), **cmds}; set_session(session)
    job.status = "done"; update_job(job)

def handle_download_all_found(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    all_results = session.found_downloads or []
    if not all_results:
        send_message(chat_id, "🚫 فایلی برای دانلود وجود ندارد.")
        job.status = "done"; update_job(job); return

    job_dir = os.path.join("jobs_data", job.job_id)
    os.makedirs(job_dir, exist_ok=True)
    send_message(chat_id, f"📦 در حال دانلود {len(all_results)} فایل...")
    downloaded_files = []
    for f in all_results:
        try:
            fname = get_filename_from_url(f['url'])
            fpath = os.path.join(job_dir, fname)
            with requests.get(f['url'], stream=True, timeout=60, headers={"User-Agent":"Mozilla/5.0"}) as r:
                r.raise_for_status()
                with open(fpath, "wb") as fh:
                    for chunk in r.iter_content(8192):
                        if get_session(chat_id).cancel_requested:
                            fh.close()
                            os.remove(fpath)
                            return
                        fh.write(chunk)
            downloaded_files.append(fpath)
        except Exception as e: safe_print(f"download_all: failed {f['url']}: {e}")
    if not downloaded_files:
        send_message(chat_id, "❌ هیچ فایلی دانلود نشد.")
        job.status = "error"; update_job(job)
        shutil.rmtree(job_dir, ignore_errors=True)
        return
    zp = os.path.join(job_dir, "all_files.zip")
    with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as zf:
        for fp in downloaded_files: zf.write(fp, os.path.basename(fp))
    parts = split_file_binary(zp, "all_files", ".zip") if os.path.getsize(zp) > ZIP_PART_SIZE else [zp]
    instr = os.path.join(job_dir, "merge.txt")
    with open(instr, "w") as f: f.write("همه‌ی فایل‌ها را دانلود کنید، سپس فایل .001 را با WinRAR یا 7-Zip باز کنید.")
    send_document(chat_id, instr, caption="📝 راهنما")
    for idx, p in enumerate(parts, 1): send_document(chat_id, p, caption=f"📦 پارت {idx}/{len(parts)}")
    job.status = "done"; update_job(job)
    shutil.rmtree(job_dir, ignore_errors=True)

# ═══════════════ شات کامل و کاوشگر ═══════════════
def handle_fullpage_screenshot(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    pw = sync_playwright().start(); browser = None
    job_dir = os.path.join("jobs_data", job.job_id)
    os.makedirs(job_dir, exist_ok=True)
    try:
        send_message(chat_id, "📸 در حال بارگذاری کامل صفحه...")
        browser = pw.chromium.launch(headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
        page = browser.new_page()
        page.goto(job.url, timeout=120000, wait_until="domcontentloaded")
        page.wait_for_timeout(5000)
        spath = os.path.join(job_dir, "fullpage.png")
        page.screenshot(path=spath, full_page=True)
        send_document(chat_id, spath, caption="✅ شات کامل (Full Page)")
        page.close()
        job.status = "done"; update_job(job)
    except Exception as e:
        send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"; update_job(job)
    finally:
        if browser: browser.close()
        pw.stop()
        shutil.rmtree(job_dir, ignore_errors=True)

def handle_interactive_scan(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    url = session.browser_url or job.url
    if not url:
        send_message(chat_id, "❌ صفحه‌ای برای کاوش باز نیست."); return
    pw = sync_playwright().start(); browser = None
    try:
        browser = pw.chromium.launch(headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
        page = browser.new_page()
        page.goto(url, timeout=60000, wait_until="domcontentloaded")
        page.wait_for_timeout(2000)
        elements = page.evaluate("""() => {
            const results = [];
            document.querySelectorAll('input[type="text"], input[type="search"], input[type="email"], input[type="url"], input[type="tel"], input[type="number"], textarea, [contenteditable="true"]').forEach((el, idx) => {
                if (el.offsetWidth === 0 && el.offsetHeight === 0) return;
                const placeholder = el.placeholder || el.getAttribute('aria-label') || el.textContent?.trim()?.substring(0, 50) || 'بدون عنوان';
                const name = el.name || el.id || '';
                const form = el.closest('form');
                const formAction = form ? form.action || '' : '';
                let submitBtn = null;
                if (form) {
                    const btn = form.querySelector('button[type="submit"], input[type="submit"], button:not([type])');
                    if (btn) submitBtn = {text: btn.textContent?.trim() || btn.value || 'ارسال', type: btn.tagName};
                }
                if (!submitBtn) {
                    const allBtns = document.querySelectorAll('button, input[type="button"], [role="button"]');
                    let closest = null, minDist = Infinity;
                    const rect = el.getBoundingClientRect();
                    allBtns.forEach(b => {
                        const br = b.getBoundingClientRect();
                        const dist = Math.hypot(br.x - rect.x, br.y - rect.y);
                        if (dist < 300 && dist < minDist) { minDist = dist; closest = b; }
                    });
                    if (closest) submitBtn = {text: closest.textContent?.trim() || closest.value || 'کلیک', type: closest.tagName};
                }
                let selector = '';
                if (el.id) selector = '#' + el.id;
                else if (el.name) selector = '[name="' + el.name + '"]';
                else selector = el.tagName + ':nth-of-type(' + (idx+1) + ')';
                results.push({
                    index: idx + 1,
                    type: el.tagName,
                    placeholder: placeholder,
                    name: name,
                    formAction: formAction,
                    submitBtn: submitBtn,
                    selector: selector
                });
            });
            return results;
        }""")
        page.close()
        if not elements:
            send_message(chat_id, "🚫 هیچ فیلد متنی در این صفحه یافت نشد.")
            job.status = "done"; update_job(job); return

        session.interactive_elements = elements
        set_session(session)
        lines = [f"🔎 **کاوشگر تعاملی ({len(elements)} فیلد یافت شد)**\n"]
        cmds = {}
        for el in elements:
            cmd = f"/t{el['index']}"
            cmds[cmd] = str(el['index'])
            lines.append(f"{el['index']}. 📝 «{el['placeholder']}» ({el['type']})")
            lines.append(f"   📌 {cmd}\n")
        send_message(chat_id, "\n".join(lines))
        session.text_links = {**(session.text_links or {}), **cmds}; set_session(session)
        job.status = "done"; update_job(job)
    except Exception as e:
        send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"; update_job(job)
    finally:
        if browser: browser.close()
        pw.stop()

def handle_interactive_execute(job):
    chat_id = job.chat_id; session = get_session(chat_id)
    extra = job.extra or {}
    element_index = extra.get("element_index", 1)
    user_text = extra.get("user_text", "")
    url = session.browser_url or job.url
    if not url:
        send_message(chat_id, "❌ صفحه‌ای باز نیست."); return
    elements = session.interactive_elements or []
    target = next((el for el in elements if el["index"] == element_index), None)
    if not target:
        send_message(chat_id, "❌ فیلد مورد نظر یافت نشد."); return
    send_message(chat_id, f"🔎 در حال جستجوی «{user_text}»...")
    pw = sync_playwright().start(); browser = None
    job_dir = os.path.join("jobs_data", job.job_id)
    os.makedirs(job_dir, exist_ok=True)
    try:
        browser = pw.chromium.launch(headless=True, args=["--no-sandbox", "--disable-dev-shm-usage"])
        page = browser.new_page()
        page.goto(url, timeout=60000, wait_until="domcontentloaded")
        page.wait_for_timeout(2000)
        page.evaluate(f"""([selector, value]) => {{
            const el = document.querySelector(selector) || document.querySelector('input[type="text"], textarea');
            if (el) {{
                el.focus();
                el.value = '';
                el.value = value;
                el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                el.dispatchEvent(new Event('change', {{ bubbles: true }}));
            }}
        }}""", [target["selector"], user_text])
        time.sleep(1)
        if target.get("submitBtn"):
            page.evaluate(f"""([btnText]) => {{
                const btns = document.querySelectorAll('button, input[type="submit"], [role="button"]');
                for (const b of btns) {{
                    if (b.textContent.trim() === btnText) {{
                        b.click(); return;
                    }}
                }}
            }}""", [target["submitBtn"]["text"]])
        else:
            page.keyboard.press("Enter")
        page.wait_for_timeout(10000)
        spath = os.path.join(job_dir, "interactive_result.png")
        page.screenshot(path=spath, full_page=True)
        send_document(chat_id, spath, caption=f"📸 نتیجه جستجوی «{user_text}»")
        page.close()
        job.status = "done"; update_job(job)
    except Exception as e:
        send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"; update_job(job)
    finally:
        if browser: browser.close()
        pw.stop()
        shutil.rmtree(job_dir, ignore_errors=True)

# ═══════════════ مدیریت پیام‌ها ═══════════════
def handle_message(chat_id, text):
    session = get_session(chat_id)
    text = text.strip()

    if is_user_banned(chat_id):
        send_message(chat_id, "🚫 شما تحریم هستید.")
        return

    if text == "/stop":
        if not session.current_job_id:
            send_message(chat_id, "⚠️ هیچ فرایندی برای توقف وجود ندارد.")
            return
        session.cancel_requested = True
        set_session(session)
        send_message(chat_id, "⏹️ درخواست توقف ثبت شد. فرایند به‌زودی متوقف خواهد شد.")
        return

    if text == "/kill":
        if not session.is_admin:
            send_message(chat_id, "⛔ دسترسی غیرمجاز.")
            return
        kill_all_jobs()
        for uid in list(inmemory_sessions.keys()):
            s = get_session(int(uid))
            s.state = "idle"
            s.current_job_id = None
            s.cancel_requested = True
            s.browser_links = None
            s.text_links = {}
            s.click_counter = 0
            set_session(s)
        send_message(chat_id, "💀 تمام فرایندهای همه کاربران متوقف و ریست شدند.",
                     reply_markup=main_menu_keyboard(session.is_admin))
        return

    if is_service_disabled() and not session.is_admin:
        send_message(chat_id, "⛔ سرویس موقتاً غیرفعال است.")
        return

    # دستورات ادمین
    if session.is_admin:
        if text.startswith("/ban"):
            parts = text.split()
            if len(parts) >= 2:
                try:
                    target = int(parts[1])
                    minutes = None
                    if len(parts) >= 3 and parts[2].lower() != "forever":
                        minutes = int(parts[2])
                    ban_user(target, minutes)
                    send_message(chat_id, f"✅ کاربر {target} تحریم شد.")
                except: send_message(chat_id, "❌ فرمت: /ban <آیدی> [مدت به دقیقه]")
            return
        if text.startswith("/unban"):
            parts = text.split()
            if len(parts) == 2:
                try:
                    target = int(parts[1])
                    if unban_user(target):
                        with flood_lock: user_ban_until.pop(target, None)
                        send_message(chat_id, f"✅ کاربر {target} از تحریم خارج شد.")
                    else: send_message(chat_id, "⛔ کاربر یافت نشد.")
                except: send_message(chat_id, "❌ فرمت: /unban <آیدی>")
            return
        if text.startswith("/addcode "):
            send_message(chat_id, "ℹ️ در این نسخه کدها داخل سورس هستند و با دستور ادمین ساخته نمی‌شوند.")
            return
        if text.startswith("/removecode "):
            send_message(chat_id, "ℹ️ حذف کد ممکن نیست؛ کدها هاردکد هستند.")
            return
        if text == "/toggleservice":
            disabled = toggle_service()
            status = "غیرفعال" if disabled else "فعال"
            send_message(chat_id, f"🔄 وضعیت سرویس: **{status}**")
            return

    if text == "/unsubscribe":
        if session.subscription == "پایه":
            send_message(chat_id, "⚠️ شما هم‌اکنون در طرح پایه هستید.")
            return
        session.subscription = "پایه"
        session.is_admin = (chat_id == ADMIN_CHAT_ID)
        set_session(session)
        send_message(chat_id, "🔓 اشتراک شما لغو شد. اکنون در طرح **پایه** هستید.",
                     reply_markup=main_menu_keyboard(session.is_admin))
        for code, cid in list(code_bindings.items()):
            if cid == chat_id:
                del code_bindings[code]
        return

    if text == "/start":
        session.state = "idle"
        session.click_counter = 0
        set_session(session)
        if session.is_admin or session.subscription != "پایه":
            send_message(chat_id, "منوی اصلی:", reply_markup=main_menu_keyboard(session.is_admin))
        else:
            kb = {"inline_keyboard": [
                [{"text": "🆓 اشتراک رایگان", "callback_data": "free_info"}],
                [{"text": "🔑 ورود کد اشتراک", "callback_data": "enter_code"}]
            ]}
            send_message(chat_id, "👋 برای شروع یکی از گزینه‌ها را انتخاب کنید:", reply_markup=kb)
        return

    if session.state == "waiting_code":
        sub = activate_subscription(chat_id, text)
        if sub:
            session.subscription = sub
            session.is_admin = (chat_id == ADMIN_CHAT_ID)
            session.state = "idle"
            set_session(session)
            send_message(chat_id, f"✅ اشتراک **{sub}** فعال شد!", reply_markup=main_menu_keyboard(session.is_admin))
        else:
            send_message(chat_id, "⛔ کد نامعتبر یا قبلاً مصرف شده است.")
        return

    if text.startswith("/t") and session.interactive_elements:
        parts = text[2:].strip().split(maxsplit=1)
        try:
            idx = int(parts[0])
            user_text = parts[1] if len(parts) > 1 else ""
            job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="interactive_execute", url=session.browser_url or "")
            job.extra = {"element_index": idx, "user_text": user_text}
            enqueue_job(job, "browser")
            send_message(chat_id, "🔎 در حال اجرای کاوشگر...")
        except:
            send_message(chat_id, "❌ فرمت نادرست. مثال: /t1 متن جستجو")
        return

    if session.state == "waiting_record_time":
        try:
            new_time = int(text)
            if not session.is_admin and (new_time < 1 or new_time > MAX_RECORD_MINUTES_USER):
                send_message(chat_id, f"⛔ زمان ضبط باید بین ۱ تا {MAX_RECORD_MINUTES_USER} دقیقه باشد.")
                return
            if session.is_admin and (new_time < 1 or new_time > MAX_RECORD_MINUTES_ADMIN):
                send_message(chat_id, f"⛔ زمان ضبط باید بین ۱ تا {MAX_RECORD_MINUTES_ADMIN} دقیقه باشد.")
                return
            session.settings.record_time = new_time
            session.state = "idle"
            set_session(session)
            send_message(chat_id, f"✅ زمان ضبط روی {new_time} دقیقه تنظیم شد.",
                         reply_markup=settings_keyboard(session.settings, session.subscription))
        except ValueError:
            send_message(chat_id, "❌ لطفاً یک عدد صحیح وارد کنید.")
        return

    if session.state == "waiting_url_crawler":
        url = text
        if not (url.startswith("http://") or url.startswith("https://")):
            send_message(chat_id, "❌ URL نامعتبر")
            return
        session.state = "idle"
        set_session(session)
        send_message(chat_id, "🕸️ خزنده در حال شروع...")
        from K import start_crawl
        threading.Thread(target=start_crawl, args=(chat_id, url, session.settings.crawler_mode, session.settings.crawler_layers, session.settings.crawler_limit), daemon=True).start()
        return

    if session.state.startswith("waiting_url_"):
        url = text
        if not (url.startswith("http://") or url.startswith("https://")):
            send_message(chat_id, "❌ URL نامعتبر"); return

        if is_direct_file_url(url):
            send_message(chat_id, "📥 این لینک یک فایل مستقیم است و برای این عملیات مناسب نیست. لطفاً یک لینک صفحه وب بفرستید.")
            return

        mode_map = {
            "waiting_url_screenshot": "screenshot",
            "waiting_url_download": "download",
            "waiting_url_browser": "browser",
            "waiting_url_record": "record_video"
        }
        mode = mode_map.get(session.state, "screenshot")
        if not check_flood(chat_id):
            send_message(chat_id, "🚫 اسپم شناسایی شد. ۱۵ دقیقه محروم هستید."); return
        if not session.is_admin and mode == "record_video" and session.subscription == "پایه":
            send_message(chat_id, "⛔ ضبط ویدیو برای کاربران پایه در دسترس نیست."); return
        if mode == "record_video": qtype = "record"
        elif mode in ("download",): qtype = "download"
        else: qtype = "browser"
        if not session.is_admin and count_user_jobs(chat_id) >= 2:
            send_message(chat_id, "🛑 صف پر است."); return
        job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode=mode, url=url, queue_type=qtype)
        enqueue_job(job, qtype)
        session.state = "idle"; session.current_job_id = job.job_id
        set_session(session)
        send_message(chat_id, "✅ در صف قرار گرفت.")
        return

    if text.startswith("/heuhshs"):
        if session.text_links and text in session.text_links:
            url = session.text_links.pop(text)
            set_session(session)
            job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="download", url=url, queue_type="download")
            enqueue_job(job, "download")
            send_message(chat_id, "📥 دانلود شروع شد...")
        else:
            send_message(chat_id, "❌ لینک مستقیم برای این دستور یافت نشد.")
        return

    if session.state == "browsing" and session.text_links and text in session.text_links:
        url = session.text_links.pop(text)
        set_session(session)
        if not check_flood(chat_id):
            send_message(chat_id, "🚫 اسپم. محروم ۱۵ دقیقه."); return
        if text.startswith("/o") or text.startswith("/d"):
            job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="download", url=url, queue_type="download")
            enqueue_job(job, "download")
        else:
            job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="browser", url=url, queue_type="browser")
            enqueue_job(job, "browser")
        return

    send_message(chat_id, "از منو استفاده کنید:", reply_markup=main_menu_keyboard(session.is_admin))

# ═══════════════ مدیریت callback ها ═══════════════
def handle_callback(cq):
    cid = cq["id"]; msg = cq.get("message"); data = cq.get("data", "")
    if not msg:
        answer_callback_query(cid)
        return
    chat_id = msg["chat"]["id"]
    session = get_session(chat_id)

    if is_service_disabled() and not session.is_admin:
        answer_callback_query(cid, "⛔ سرویس غیرفعال است.")
        return

    if is_user_banned(chat_id):
        answer_callback_query(cid, "🚫 محروم هستید.")
        return

    if not session.is_admin and not check_flood(chat_id):
        answer_callback_query(cid, "🚫 اسپم. ۱۵ دقیقه محروم.", show_alert=True)
        return

    if data == "menu_help":
        help_text = (
            "📖 **راهنمای ربات**\n\n"
            "🧭 **مرورگر:** لینک بده، صفحه رو ببین، لینک‌ها و ویدیوهاش رو استخراج کن.\n"
            "📸 **شات:** از صفحه عکس بگیر.\n"
            "📥 **دانلود:** لینک فایل یا صفحه بده، دانلود کن.\n"
            "🎬 **ضبط:** از صفحه ویدئو بگیر.\n"
            "🕸️ **خزنده وحشی:** جستجوی عمیق و دسته‌بندی همه فایل‌ها و متون.\n"
            "🪟 **حل کپچا:** در مرورگر فعال، کلیک خودکار و یافتن لینک دانلود.\n"
            "⚙️ **تنظیمات:** شخصی‌سازی همه چیز.\n"
            "/stop : توقف فرایند جاری.\n"
            "/kill : (ادمین) توقف همه کارهای همه کاربران."
        )
        send_message(chat_id, help_text, reply_markup={"inline_keyboard": [[{"text": "🔙 بازگشت", "callback_data": "back_main"}]]})
        return

    if data == "menu_crawler":
        if not session.is_admin and session.subscription not in ("طلایی", "الماسی"):
            answer_callback_query(cid, "⛔ این قابلیت فقط برای سطوح طلایی و الماسی در دسترس است.")
            return
        session.state = "waiting_url_crawler"
        set_session(session)
        send_message(chat_id, "🕸️ لطفاً آدرس شروع خزنده وحشی را بفرستید:")
        return

    if data == "free_info":
        send_message(chat_id, "برای تهیه اشتراک به @MrHadi3 پیام دهید.")
        return

    if data == "enter_code":
        session.state = "waiting_code"; set_session(session)
        send_message(chat_id, "🔑 لطفاً کد اشتراک خود را وارد کنید:")
        return

    if data == "menu_screenshot":
        if session.subscription == "پایه" and not session.is_admin:
            answer_callback_query(cid, "⛔ نیاز به اشتراک."); return
        session.state = "waiting_url_screenshot"; set_session(session); send_message(chat_id, "📸 URL:")
    elif data == "menu_download":
        if session.subscription == "پایه" and not session.is_admin:
            answer_callback_query(cid, "⛔ نیاز به اشتراک."); return
        session.state = "waiting_url_download"; set_session(session); send_message(chat_id, "📥 URL:")
    elif data == "menu_browser":
        if session.subscription == "پایه" and not session.is_admin:
            answer_callback_query(cid, "⛔ نیاز به اشتراک."); return
        session.state = "waiting_url_browser"; set_session(session); send_message(chat_id, "🧭 URL:")
    elif data == "menu_record":
        if session.subscription == "پایه" and not session.is_admin:
            answer_callback_query(cid, "⛔ نیاز به اشتراک."); return
        session.state = "waiting_url_record"; set_session(session); send_message(chat_id, "🎬 لینک:")
    elif data == "menu_settings":
        kb = settings_keyboard(session.settings, session.subscription)
        msg = f"⚙️ **تنظیمات**\n\n⏱️ زمان ضبط (دقیقه): {session.settings.record_time}\n📥 دانلود: {'سریع' if session.settings.default_download_mode == 'stream' else 'عادی'}\n🌐 حالت: {session.settings.browser_mode}\n🎬 رفتار ضبط: {'کلیک' if session.settings.record_behavior == 'click' else 'اسکرول'}\n🎞️ فرمت: {session.settings.video_format.upper()}\n📺 کیفیت: {session.settings.video_resolution}\n📦 ارسال: {session.settings.video_delivery}"
        result = send_message(chat_id, msg, reply_markup=kb)
        if result and "message_id" in result:
            session.last_settings_msg_id = result["message_id"]; set_session(session)
    elif data == "menu_admin":
        if session.is_admin: admin_panel(chat_id)
        else: answer_callback_query(cid, "دسترسی غیرمجاز")
    elif data in ("set_dlmode", "set_brwmode", "set_deep", "set_recbeh", "set_vfmt", "set_incognito", "set_viddel", "set_resolution", "set_audio"):
        _settings_toggle(chat_id, session, data, cid)
    elif data == "set_rec":
        session.state = "waiting_record_time"; set_session(session)
        send_message(chat_id, "⏱️ زمان ضبط را به **دقیقه** وارد کنید (۱ تا ۶۰ برای ادمین، ۱ تا ۱۵ برای کاربران عادی):")
    elif data == "back_main":
        send_message(chat_id, "منوی اصلی:", reply_markup=main_menu_keyboard(session.is_admin))
    elif data == "admin_toggleservice":
        if session.is_admin:
            disabled = toggle_service()
            status = "غیرفعال" if disabled else "فعال"
            answer_callback_query(cid, f"سرویس {status} شد.")
            admin_panel(chat_id)
        else: answer_callback_query(cid, "دسترسی غیرمجاز")
    elif data == "admin_users":
        if session.is_admin: list_users(chat_id)
        else: answer_callback_query(cid, "دسترسی غیرمجاز")

    elif data.startswith("req2x_"):
        jid = data[6:]; job = find_job(jid)
        if job and job.status == "done":
            enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="2x_screenshot", url=job.url, queue_type="browser"), "browser")
    elif data.startswith("req4k_"):
        jid = data[6:]; job = find_job(jid)
        if job and job.status == "done":
            enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="4k_screenshot", url=job.url, queue_type="browser"), "browser")
    elif data.startswith("dlzip_") or data.startswith("dlraw_"):
        jid = data[6:] if data.startswith("dlzip_") else data[6:]; job = find_job(jid)
        if job and job.extra:
            job.extra["pack_zip"] = data.startswith("dlzip_"); job.status = "done"; update_job(job)
            enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="download_execute", url=job.url, extra=job.extra, queue_type="download"), "download")
    elif data.startswith("dlblindzip_") or data.startswith("dlblindra_"):
        jid = data[11:] if data.startswith("dlblindzip_") else data[11:]; job = find_job(jid)
        if job and job.extra and "file_path" in job.extra:
            job.extra["pack_zip"] = data.startswith("dlblindzip_"); job.status = "done"; update_job(job)
            enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="download_execute", url=job.url, extra=job.extra, queue_type="download"), "download")
    elif data.startswith("canceljob_"):
        jid = data[10:]; job = find_job(jid)
        if job: job.status = "cancelled"; update_job(job)
        send_message(chat_id, "❌ لغو شد.", reply_markup=main_menu_keyboard(session.is_admin))
    elif data.startswith("nav_"):
        parts = data.split("_", 2)
        if len(parts) >= 3:
            cb = f"{parts[0]}_{parts[1]}_{parts[2]}"
            with callback_map_lock: url = callback_map.pop(cb, None)
            if url:
                if session.is_admin or count_user_jobs(chat_id) < 2:
                    enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="browser", url=url, queue_type="browser"), "browser")
                else: answer_callback_query(cid, "🛑 صف پر است.")
    elif data.startswith("dlvid_"):
        parts = data.split("_", 2)
        if len(parts) >= 3:
            cb = f"{parts[0]}_{parts[1]}_{parts[2]}"
            with callback_map_lock: url = callback_map.pop(cb, None)
            if url:
                if session.is_admin or count_user_jobs(chat_id) < 2:
                    enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="download", url=url, queue_type="download"), "download")
                else: answer_callback_query(cid, "🛑 صف پر است.")
    elif data.startswith("scvid_"):
        enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="scan_videos", url="", queue_type="browser"), "browser")
    elif data.startswith("scdl_"):
        enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="scan_downloads", url="", queue_type="browser"), "browser")
    elif data.startswith("extcmd_"):
        enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="extract_commands", url="", queue_type="browser"), "browser")
    elif data.startswith("sman_"):
        enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="smart_analyze", url="", queue_type="browser"), "browser")
    elif data.startswith("srcan_"):
        enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="source_analyze", url="", queue_type="browser"), "browser")
    elif data.startswith("recvid_"):
        if session.browser_url:
            if session.is_admin or count_user_jobs(chat_id) < 2:
                enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="record_video", url=session.browser_url, queue_type="record"), "record")
            else: answer_callback_query(cid, "🛑 صف پر است.")
        else:
            answer_callback_query(cid, "❌ مرورگری باز نیست.")
    elif data.startswith("fullshot_"):
        if session.browser_url:
            if session.is_admin or count_user_jobs(chat_id) < 2:
                enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="fullpage_screenshot", url=session.browser_url, queue_type="browser"), "browser")
            else: answer_callback_query(cid, "🛑 صف پر است.")
    elif data.startswith("dlweb_"):
        if session.browser_url:
            if session.is_admin or count_user_jobs(chat_id) < 2:
                enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="download_website", url=session.browser_url, queue_type="download"), "download")
            else: answer_callback_query(cid, "🛑 صف پر است.")
    elif data.startswith("intscan_"):
        if session.browser_url:
            if session.is_admin or count_user_jobs(chat_id) < 2:
                enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="interactive_scan", url=session.browser_url, queue_type="browser"), "browser")
            else: answer_callback_query(cid, "🛑 صف پر است.")
    elif data.startswith("bpg_"):
        parts = data.split("_")
        if len(parts) == 3:
            page = int(parts[2]); session.browser_page = page; set_session(session)
            send_browser_page(chat_id, page_num=page)
    elif data.startswith("dfpg_"):
        parts = data.split("_")
        if len(parts) == 3:
            page = int(parts[2]); session.found_downloads_page = page; set_session(session)
            send_found_downloads_page(chat_id, page)
    elif data == "close_downloads":
        session.found_downloads = None; session.found_downloads_page = 0; set_session(session)
        send_message(chat_id, "📦 نتایج جستجو بسته شد.", reply_markup=main_menu_keyboard(session.is_admin))
    elif data.startswith("dlall_"):
        enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="download_all_found", url="", queue_type="download"), "download")
    elif data.startswith("adblock_"):
        parsed_url = urlparse(session.browser_url or "")
        current_domain = parsed_url.netloc.lower()
        if not current_domain:
            answer_callback_query(cid, "دامنه‌ای برای مسدودسازی شناسایی نشد."); return
        if session.ad_blocked_domains is None: session.ad_blocked_domains = []
        if current_domain in session.ad_blocked_domains:
            session.ad_blocked_domains.remove(current_domain)
            answer_callback_query(cid, "🛡️ مسدودساز غیرفعال شد.")
        else:
            session.ad_blocked_domains.append(current_domain)
            answer_callback_query(cid, "🛡️ مسدودساز فعال شد.")
        set_session(session)
        send_browser_page(chat_id, page_num=session.browser_page)
    elif data.startswith("closebrowser_"):
        session.state = "idle"; session.click_counter = 0
        session.browser_links = None; session.browser_url = None
        session.text_links = {}
        with callback_map_lock:
            to_remove = [k for k, v in callback_map.items() if k.startswith(f"nav_{chat_id}_") or k.startswith(f"dlvid_{chat_id}_")]
            for k in to_remove: del callback_map[k]
        set_session(session)
        send_message(chat_id, "🧭 بسته شد.", reply_markup=main_menu_keyboard(session.is_admin))
    elif data.startswith("captcha_"):
        if session.browser_url:
            job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="captcha", url=session.browser_url, queue_type="browser")
            enqueue_job(job, "browser")
            answer_callback_query(cid, "🪟 در حال بررسی کپچا...")
        else:
            answer_callback_query(cid, "❌ مرورگری باز نیست.")
    else:
        answer_callback_query(cid)

def _settings_toggle(chat_id, session, data, cid):
    if data == "set_dlmode": session.settings.default_download_mode = "stream" if session.settings.default_download_mode == "store" else "store"
    elif data == "set_brwmode": modes = ["text", "media", "explorer"]; idx = modes.index(session.settings.browser_mode); session.settings.browser_mode = modes[(idx+1)%3]
    elif data == "set_deep": session.settings.deep_scan_mode = "everything" if session.settings.deep_scan_mode == "logical" else "logical"
    elif data == "set_recbeh": session.settings.record_behavior = "scroll" if session.settings.record_behavior == "click" else "click"
    elif data == "set_vfmt": formats = ["webm", "mkv", "mp4"]; idx = formats.index(session.settings.video_format); session.settings.video_format = formats[(idx+1)%3]
    elif data == "set_incognito": session.settings.incognito_mode = not session.settings.incognito_mode
    elif data == "set_viddel": session.settings.video_delivery = "zip" if session.settings.video_delivery == "split" else "split"
    elif data == "set_resolution": resolutions = ["480p", "720p", "1080p", "4k"]; idx = resolutions.index(session.settings.video_resolution) if session.settings.video_resolution in resolutions else 1; session.settings.video_resolution = resolutions[(idx+1)%len(resolutions)]
    elif data == "set_audio": session.settings.audio_enabled = not session.settings.audio_enabled
    set_session(session)
    answer_callback_query(cid, "✅ تنظیم شد.")
    if session.last_settings_msg_id:
        kb = settings_keyboard(session.settings, session.subscription)
        edit_message_reply_markup(chat_id, session.last_settings_msg_id, kb)

# ═══════════════ پنل ادمین و لیست کاربران ═══════════════
def admin_panel(chat_id):
    try:
        mem = subprocess.run(['free', '-m'], stdout=subprocess.PIPE, text=True).stdout.strip()
        disk = subprocess.run(['df', '-h'], stdout=subprocess.PIPE, text=True).stdout.strip()
        uptime = subprocess.run(['uptime'], stdout=subprocess.PIPE, text=True).stdout.strip()
        active_users = len(inmemory_sessions)
        status = "⛔ غیرفعال" if is_service_disabled() else "✅ فعال"
        msg = f"🛠️ **پنل ادمین**\n\n🔧 **وضعیت سرویس:** {status}\n\n💾 **حافظه:**\n{mem}\n\n📀 **دیسک:**\n{disk}\n\n⏱️ **آپ‌تایم:**\n{uptime}\n\n👥 **کاربران فعال:** {active_users}"
        kb = {"inline_keyboard": [
            [{"text": "👥 کاربران", "callback_data": "admin_users"}, {"text": "🔄 تغییر وضعیت", "callback_data": "admin_toggleservice"}],
            [{"text": "🔙 بازگشت", "callback_data": "back_main"}]
        ]}
        send_message(chat_id, msg, reply_markup=kb)
    except: send_message(chat_id, "❌ خطا در بارگذاری اطلاعات")

def list_users(chat_id):
    if not inmemory_sessions:
        send_message(chat_id, "ℹ️ کاربری وجود ندارد.")
        return
    lines = ["👥 **لیست کاربران:**"]
    for uid, sdata in inmemory_sessions.items():
        sub = sdata.get("subscription", "پایه")
        lines.append(f"🆔 `{uid}` – {sub}")
    send_message(chat_id, "\n".join(lines))

# ═══════════════ حلقه‌های اصلی ═══════════════
def clean_old_links():
    while True:
        try:
            now = time.time()
            for uid, sdata in list(inmemory_sessions.items()):
                if "last_browser_time" in sdata and now - sdata["last_browser_time"] > 1200:
                    sdata["browser_links"] = None
                    sdata["browser_url"] = None
                    sdata["text_links"] = {}
                    sdata["last_browser_time"] = 0
                    with callback_map_lock:
                        to_remove = [k for k in callback_map if k.startswith(f"nav_{uid}_") or k.startswith(f"dlvid_{uid}_")]
                        for k in to_remove: del callback_map[k]
        except: pass
        time.sleep(60)

def polling_loop(stop_event):
    offset = None
    safe_print("[Polling] start")

    try:
        first_updates = get_updates(timeout=0)
        if first_updates:
            offset = first_updates[-1]["update_id"] + 1
            safe_print(f"[Poll] skipping {len(first_updates)} old updates, starting from offset {offset}")
        else:
            safe_print("[Poll] no old updates found.")
    except Exception as e:
        safe_print(f"[Poll] could not skip old updates: {e}")

    while not stop_event.is_set():
        try:
            updates = get_updates(offset, LONG_POLL_TIMEOUT)
        except Exception as e:
            safe_print(f"Poll error: {e}")
            time.sleep(5)
            continue
        for upd in updates:
            offset = upd["update_id"] + 1
            try:
                if "message" in upd and "text" in upd["message"]:
                    handle_message(upd["message"]["chat"]["id"], upd["message"]["text"])
                elif "callback_query" in upd:
                    handle_callback(upd["callback_query"])
            except Exception as e:
                safe_print(f"Update handling error: {e}")
                safe_print(traceback.format_exc())
    safe_print("[Polling] متوقف شد")

def main():
    os.makedirs("jobs_data", exist_ok=True)
    global admin_bans
    admin_bans = {}
    stop_event = threading.Event()

    for i in range(2):
        threading.Thread(target=worker_loop, args=(i, stop_event, "browser"), daemon=True).start()
    for i in range(2):
        threading.Thread(target=worker_loop, args=(i+2, stop_event, "download"), daemon=True).start()
    for i in range(2):
        threading.Thread(target=worker_loop, args=(i+4, stop_event, "record"), daemon=True).start()

    threading.Thread(target=polling_loop, args=(stop_event,), daemon=True).start()
    threading.Thread(target=clean_old_links, daemon=True).start()
    safe_print("✅ Bot27 اجرا شد")
    try:
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        stop_event.set()

if __name__ == "__main__":
    main()
