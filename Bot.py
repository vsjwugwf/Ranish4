#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Bot - نسخهٔ نهایی (asyncio, Playwright Async, Git Persistence)
قابلیت‌ها:
- دو مرورگر اشتراکی (عمومی + ضبط)
- مرورگر ۳ حالته (text / media / explorer)
- اسکرین‌شات (عادی، 2x Zoom، 4K)
- دانلود هوشمند با ۳ حالت: عادی، سریع (stream)، ADM (چندبخشی)
- ضبط ویدیو با تنظیمات پیشرفته (رزولوشن، صدا، فرمت، delivery)
- پنل ادمین شیشه‌ای (اضافه/حذف کد، بن، سرویس)
- خزنده وحشی با منوی کامل تنظیمات (K.py)
- ذخیره‌سازی پایدار روی گیت‌هاب (subscriptions.json)
- پاکسازی خودکار Contextها و جلسات مرورگر (۲۰ دقیقه)
- محدودیت مصرف بر اساس سطح اشتراک (free/bronze/plus/pro)
"""

import os, sys, json, time, math, uuid, re, hashlib, zipfile, shutil
import asyncio, subprocess, traceback
from dataclasses import dataclass, asdict, field
from typing import Dict, Any, Optional, List, Tuple
from urllib.parse import urlparse, urljoin, unquote

import aiohttp
from bs4 import BeautifulSoup
from playwright.async_api import async_playwright

# ═══════════ تنظیمات ثابت ═══════════
BOT_TOKEN = os.getenv("BALE_BOT_TOKEN", "").strip()
if not BOT_TOKEN:
    print("FATAL: BALE_BOT_TOKEN not set")
    sys.exit(1)

API_BASE = f"https://tapi.bale.ai/bot{BOT_TOKEN}"
REQUEST_TIMEOUT = aiohttp.ClientTimeout(total=30)
ZIP_PART_SIZE = 19 * 1024 * 1024

ADMIN_CHAT_ID = 46829437

PLAN_LIMITS = {
    "free": {
        "browser": (2, 3600, None), "screenshot": (2, 3600, None),
        "2x_screenshot": (0, 3600, None), "4k_screenshot": (0, 3600, None),
        "download": (1, 3600, 10 * 1024 * 1024), "record_video": (0, 3600, None),
        "scan_downloads": (0, 3600, None), "scan_videos": (0, 3600, None),
        "download_website": (0, 3600, None), "extract_commands": (0, 3600, None),
    },
    "bronze": {
        "browser": (5, 3600, None), "screenshot": (2, 3600, None),
        "2x_screenshot": (1, 3600, None), "4k_screenshot": (1, 3600, None),
        "download": (2, 3600, 100 * 1024 * 1024), "record_video": (1, 3600, None),
        "scan_downloads": (1, 3600, None), "scan_videos": (1, 3600, None),
        "download_website": (0, 3600, None), "extract_commands": (1, 3600, None),
    },
    "plus": {
        "browser": (10, 3600, None), "screenshot": (10, 3600, None),
        "2x_screenshot": (5, 3600, None), "4k_screenshot": (3, 3600, None),
        "download": (5, 3600, 600 * 1024 * 1024), "record_video": (3, 3600, None),
        "scan_downloads": (2, 3600, None), "scan_videos": (5, 3600, None),
        "download_website": (1, 3600, None), "extract_commands": (3, 3600, None),
    },
    "pro": {
        "browser": (999, 3600, None), "screenshot": (999, 3600, None),
        "2x_screenshot": (999, 3600, None), "4k_screenshot": (999, 3600, None),
        "download": (999, 3600, None), "record_video": (999, 3600, None),
        "scan_downloads": (999, 3600, None), "scan_videos": (999, 3600, None),
        "download_website": (3, 86400, None), "extract_commands": (999, 3600, None),
    },
}

ALLOWED_RESOLUTIONS = {
    "480p": (854, 480), "720p": (1280, 720),
    "1080p": (1920, 1080), "4k": (3840, 2160),
}
RES_REQUIREMENTS = {
    "480p": ["free","bronze","plus","pro"],
    "720p": ["bronze","plus","pro"],
    "1080p": ["plus","pro"],
    "4k": ["pro"],
}

AD_DOMAINS = {"doubleclick.net","googleadservices.com","googlesyndication.com","adservice.google.com"}
BLOCKED_AD_KEYWORDS = {"ad","banner","popup","sponsor","track","analytics"}

DATA_DIR = "data"
os.makedirs(DATA_DIR, exist_ok=True)
SUBSCRIPTIONS_FILE = os.path.join(DATA_DIR, "subscriptions.json")

# قفل‌ها
session_lock = asyncio.Lock()
sub_lock = asyncio.Lock()
callback_map_lock = asyncio.Lock()

# حافظهٔ سراسری
sessions: Dict[int, "SessionState"] = {}
callback_map: Dict[str, str] = {}
subscriptions_data = None
service_disabled = False

# صف‌ها
general_queue = asyncio.Queue()
record_queue = asyncio.Queue()

# مرورگرها
general_playwright = None
general_browser = None
general_contexts: Dict[str, Any] = {}
record_playwright = None
record_browser = None

# کدهای پشتیبان
HARDCODED_CODES = {
    "bronze": ["BR001","BR002","BR003","BR004","BR005"],
    "plus":   ["PL001","PL002","PL003","PL004","PL005"],
    "pro":    ["PR001","PR002","PR003","PR004","PR005"],
}

# ═══════════ مدل‌های داده ═══════════
@dataclass
class UserSettings:
    record_time: int = 20
    default_download_mode: str = "store"      # store / stream / adm
    browser_mode: str = "text"                # text / media / explorer
    deep_scan_mode: str = "logical"
    record_behavior: str = "click"
    audio_enabled: bool = False
    video_format: str = "webm"
    incognito_mode: bool = False
    video_delivery: str = "split"
    video_resolution: str = "720p"
    # تنظیمات خزنده
    crawler_mode: str = "normal"
    crawler_layers: int = 2
    crawler_limit: int = 0
    crawler_max_time: int = 20
    crawler_filters: Dict[str, bool] = field(default_factory=lambda: {
        "image": True, "video": True, "archive": True, "pdf": True, "unknown": True
    })
    crawler_adblock: bool = True
    crawler_sitemap: bool = False
    crawler_priority: bool = False
    crawler_js: bool = False

@dataclass
class SessionState:
    chat_id: int
    state: str = "idle"
    is_admin: bool = False
    subscription: str = "free"
    current_job_id: Optional[str] = None
    browser_url: Optional[str] = None
    last_interaction: float = field(default_factory=time.time)
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
    last_crawler_msg_id: Optional[str] = None
    interactive_elements: Optional[List[Dict[str, Any]]] = None
    usage: Dict[str, List[float]] = field(default_factory=dict)
    last_browser_time: float = 0.0
    crawler_active: bool = False
    crawler_pending_url: Optional[str] = None

@dataclass
class Job:
    job_id: str
    chat_id: int
    mode: str
    url: str
    status: str = "queued"
    created_at: float = field(default_factory=time.time)
    updated_at: float = field(default_factory=time.time)
    error_message: Optional[str] = None
    extra: Optional[Dict[str, Any]] = None
    started_at: Optional[float] = None
    queue_type: str = "general"

# ═══════════ ابزارهای کمکی ═══════════
def load_json(filepath, default=None):
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            return json.load(f)
    except:
        return default if default is not None else {}

def save_json(filepath, data):
    tmp = filepath + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
    os.replace(tmp, filepath)

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

def get_filename_from_url(url):
    path = unquote(urlparse(url).path)
    name = os.path.basename(path)
    return name if name and '.' in name else "downloaded_file"

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
            parts = sorted([os.path.join(d, f) for f in os.listdir(d)
                            if f.startswith(f"{prefix}_part") and f.endswith(ext)])
            if parts:
                return parts
        except Exception as e:
            safe_log(f"ffmpeg segment failed: {e}")
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

def safe_log(msg):
    try:
        with open("bot.log", "a", encoding="utf-8") as f:
            f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} {msg}\n")
    except:
        pass
    print(msg, flush=True)
    
# ═══════════ API بله (async) ═══════════
async def bale_request(method: str, params: dict = None, files: dict = None) -> Optional[dict]:
    url = f"{API_BASE}/{method}"
    async with aiohttp.ClientSession(timeout=REQUEST_TIMEOUT) as session:
        try:
            if files:
                data = aiohttp.FormData()
                for k, v in (params or {}).items():
                    data.add_field(k, str(v))
                for k, v in files.items():
                    data.add_field(k, v[1], filename=v[0])
                async with session.post(url, data=data) as resp:
                    if resp.status == 200:
                        j = await resp.json()
                        if j.get("ok"):
                            return j["result"]
            else:
                async with session.post(url, json=params or {}) as resp:
                    if resp.status == 200:
                        j = await resp.json()
                        if j.get("ok"):
                            return j["result"]
        except Exception as e:
            safe_log(f"API {method} error: {e}")
    return None

async def send_message(chat_id, text, reply_markup=None):
    params = {"chat_id": chat_id, "text": text}
    if reply_markup:
        params["reply_markup"] = json.dumps(reply_markup)
    return await bale_request("sendMessage", params)

async def edit_message_reply_markup(chat_id, message_id, reply_markup):
    params = {"chat_id": chat_id, "message_id": message_id,
              "reply_markup": json.dumps(reply_markup)}
    return await bale_request("editMessageReplyMarkup", params)

async def send_document(chat_id, file_path, caption=""):
    if not os.path.exists(file_path):
        return None
    with open(file_path, "rb") as fh:
        content = fh.read()
    filename = os.path.basename(file_path)
    files = {"document": (filename, content)}
    return await bale_request("sendDocument",
                              {"chat_id": chat_id, "caption": caption},
                              files)

async def answer_callback_query(cq_id, text="", show_alert=False):
    return await bale_request("answerCallbackQuery",
                              {"callback_query_id": cq_id, "text": text, "show_alert": show_alert})

async def get_updates(offset=None, timeout=50):
    params = {"timeout": timeout}
    if offset:
        params["offset"] = offset
    return await bale_request("getUpdates", params) or []

# ═══════════ مدیریت اشتراک‌ها (Git Persistence) ═══════════
async def git_commit_and_push(filepath: str, message: str = "auto: update subscriptions"):
    if not os.getenv("GITHUB_TOKEN") and not os.getenv("GITHUB_ACTIONS"):
        return
    try:
        repo = os.getenv("GITHUB_REPOSITORY", "")
        token = os.getenv("GITHUB_TOKEN", "")
        if not repo or not token:
            return
        subprocess.run(["git", "config", "user.name", "bot"], check=False)
        subprocess.run(["git", "config", "user.email", "bot@no-reply.com"], check=False)
        subprocess.run(["git", "add", filepath], check=False)
        subprocess.run(["git", "commit", "-m", message], check=False)
        remote_url = f"https://x-access-token:{token}@github.com/{repo}.git"
        subprocess.run(["git", "push", remote_url, "HEAD:main"], check=False)
        safe_log(f"Git pushed: {filepath}")
    except Exception as e:
        safe_log(f"Git push failed: {e}")

async def load_subscriptions() -> dict:
    global subscriptions_data
    data = load_json(SUBSCRIPTIONS_FILE)
    if not data:
        data = {
            "valid_codes": HARDCODED_CODES.copy(),
            "user_levels": {},
            "bans": {}
        }
        save_json(SUBSCRIPTIONS_FILE, data)
    subscriptions_data = data
    return data

async def save_subscriptions(data: dict = None):
    global subscriptions_data
    if data is None:
        data = subscriptions_data
    if data is None:
        return
    async with sub_lock:
        save_json(SUBSCRIPTIONS_FILE, data)
        subscriptions_data = data
    asyncio.create_task(git_commit_and_push(SUBSCRIPTIONS_FILE))

async def get_user_level(chat_id: int) -> str:
    if chat_id == ADMIN_CHAT_ID:
        return "pro"
    data = await load_subscriptions()
    return data.get("user_levels", {}).get(str(chat_id), "free")

async def set_user_level(chat_id: int, level: str):
    data = await load_subscriptions()
    data.setdefault("user_levels", {})[str(chat_id)] = level
    await save_subscriptions(data)

async def activate_code(chat_id: int, code: str) -> Optional[str]:
    code = code.strip()
    data = await load_subscriptions()
    codes = data.get("valid_codes", HARDCODED_CODES)
    for level, codelist in codes.items():
        if code in codelist:
            codelist.remove(code)
            await save_subscriptions(data)
            await set_user_level(chat_id, level)
            return level
    return None

async def add_code(level: str, code: str) -> bool:
    data = await load_subscriptions()
    codes = data.setdefault("valid_codes", HARDCODED_CODES.copy())
    if level not in codes:
        return False
    if code in codes[level]:
        return False
    codes[level].append(code)
    await save_subscriptions(data)
    return True

async def remove_code(code: str) -> Optional[str]:
    data = await load_subscriptions()
    codes = data.get("valid_codes", {})
    for level, codelist in codes.items():
        if code in codelist:
            codelist.remove(code)
            await save_subscriptions(data)
            return level
    return None

async def ban_user(chat_id: int, duration_minutes: Optional[int] = None):
    data = await load_subscriptions()
    bans = data.setdefault("bans", {})
    if duration_minutes is None:
        bans[str(chat_id)] = "forever"
    else:
        bans[str(chat_id)] = time.time() + duration_minutes * 60
    await save_subscriptions(data)

async def unban_user(chat_id: int) -> bool:
    data = await load_subscriptions()
    bans = data.get("bans", {})
    if str(chat_id) in bans:
        del bans[str(chat_id)]
        await save_subscriptions(data)
        return True
    return False

async def is_banned(chat_id: int) -> bool:
    if chat_id == ADMIN_CHAT_ID:
        return False
    data = await load_subscriptions()
    bans = data.get("bans", {})
    entry = bans.get(str(chat_id))
    if entry is None:
        return False
    if entry == "forever":
        return True
    if time.time() > entry:
        del bans[str(chat_id)]
        asyncio.create_task(save_subscriptions(data))
        return False
    return True

async def check_rate_limit(chat_id: int, mode: str, file_size_bytes: Optional[int] = None) -> Optional[str]:
    if chat_id == ADMIN_CHAT_ID:
        return None
    level = await get_user_level(chat_id)
    limits = PLAN_LIMITS.get(level, PLAN_LIMITS["free"])
    mode_key = mode if mode not in ("browser", "browser_click") else "browser"
    limit = limits.get(mode_key)
    if not limit:
        return f"⛔ این قابلیت برای سطح «{level}» در دسترس نیست."
    max_count, window_seconds, max_size = limit
    if max_size is not None and file_size_bytes is not None and file_size_bytes > max_size:
        max_mb = max_size / (1024 * 1024)
        return f"📦 حجم فایل ({file_size_bytes/(1024*1024):.1f}MB) بیش از حد مجاز ({max_mb:.0f}MB) برای سطح «{level}» است."
    if max_count >= 999:
        return None
    session = await get_session(chat_id)
    async with session_lock:
        usage = session.usage.get(mode_key, [])
        now = time.time()
        cutoff = now - window_seconds
        recent = [t for t in usage if t > cutoff]
        if len(recent) >= max_count:
            return f"⏰ محدودیت ساعتی: حداکثر {max_count} بار در ساعت (سطح «{level}»)."
        usage.append(now)
        session.usage[mode_key] = usage
        await set_session(session)
    return None

# ═══════════ مدیریت نشست‌ها ═══════════
async def get_session(chat_id: int) -> SessionState:
    async with session_lock:
        if chat_id in sessions:
            return sessions[chat_id]
        s = SessionState(chat_id=chat_id)
        if chat_id == ADMIN_CHAT_ID:
            s.is_admin = True
            s.subscription = "pro"
        else:
            s.subscription = await get_user_level(chat_id)
        sessions[chat_id] = s
        return s

async def set_session(session: SessionState):
    async with session_lock:
        sessions[session.chat_id] = session

# ═══════════ منوها ═══════════
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
    dlm = {"store": "عادی 💾", "stream": "سریع ⚡", "adm": "ADM ⚡⚡"}[settings.default_download_mode]
    mode = {"text": "📄 متن", "media": "🎬 مدیا", "explorer": "🔍 جستجوگر"}[settings.browser_mode]
    deep = "🧠 منطقی" if settings.deep_scan_mode == "logical" else "🗑 همه چیز"
    rec_behavior = "🖱️ کلیک" if settings.record_behavior == "click" else "📜 اسکرول"
    audio = "🔊 با صدا" if settings.audio_enabled else "🔇 بی‌صدا"
    vfmt = settings.video_format.upper()
    incognito = "🕶️ ناشناس" if settings.incognito_mode else "👤 عادی"
    delivery = "ZIP 📦" if settings.video_delivery == "zip" else "تکه‌ای 🧩"
    res = settings.video_resolution
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
        [{"text": "🔙 بازگشت", "callback_data": "back_main"}]
    ]
    return {"inline_keyboard": kb}

def crawler_settings_keyboard(settings: UserSettings):
    fil = settings.crawler_filters
    return {"inline_keyboard": [
        [{"text": f"📊 حالت: {settings.crawler_mode}", "callback_data": "crawler_mode"}],
        [{"text": f"🔢 لایه‌ها: {settings.crawler_layers}", "callback_data": "crawler_layers"}],
        [{"text": f"📄 صفحات: {'خودکار' if settings.crawler_limit==0 else settings.crawler_limit}", "callback_data": "crawler_limit"}],
        [{"text": f"⏱️ زمان: {settings.crawler_max_time}m", "callback_data": "crawler_time"}],
        [{"text": f"🖼️ تصاویر: {'✅' if fil['image'] else '❌'}", "callback_data": "crawler_filter_image"}],
        [{"text": f"🎬 ویدیوها: {'✅' if fil['video'] else '❌'}", "callback_data": "crawler_filter_video"}],
        [{"text": f"📦 فشرده: {'✅' if fil['archive'] else '❌'}", "callback_data": "crawler_filter_archive"}],
        [{"text": f"📄 PDF: {'✅' if fil['pdf'] else '❌'}", "callback_data": "crawler_filter_pdf"}],
        [{"text": f"❓ ناشناخته: {'✅' if fil['unknown'] else '❌'}", "callback_data": "crawler_filter_unknown"}],
        [{"text": f"🛡️ ضد تبلیغ: {'✅' if settings.crawler_adblock else '❌'}", "callback_data": "crawler_adblock"}],
        [{"text": f"📋 Sitemap: {'✅' if settings.crawler_sitemap else '❌'}", "callback_data": "crawler_sitemap"}],
        [{"text": f"⚡ اولویت‌بندی: {'✅' if settings.crawler_priority else '❌'}", "callback_data": "crawler_priority"}],
        [{"text": f"🌐 JS: {'✅' if settings.crawler_js else '❌'}", "callback_data": "crawler_js"}],
        [{"text": "▶️ شروع خزنده", "callback_data": "crawler_start"}],
        [{"text": "🔙 بازگشت", "callback_data": "back_main"}]
    ]}
# ═══════════ مدیریت مرورگرهای اشتراکی (Playwright Async) ═══════════

async def init_browsers():
    global general_playwright, general_browser, record_playwright, record_browser
    safe_log("Launching general browser...")
    general_playwright = await async_playwright().start()
    general_browser = await general_playwright.chromium.launch(
        headless=True,
        args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu",
              "--autoplay-policy=no-user-gesture-required"]
    )

    safe_log("Launching record browser...")
    record_playwright = await async_playwright().start()
    record_browser = await record_playwright.chromium.launch(
        headless=True,
        args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu",
              "--autoplay-policy=no-user-gesture-required"]
    )

async def get_user_context(chat_id: int, incognito: bool = False):
    key = f"{chat_id}{'_incognito' if incognito else ''}"
    async with session_lock:
        if key in general_contexts:
            ctx_info = general_contexts[key]
            if time.time() - ctx_info["last_used"] > 1200:
                try:
                    await ctx_info["context"].close()
                except:
                    pass
                del general_contexts[key]
            else:
                ctx_info["last_used"] = time.time()
                return ctx_info["context"]

    context = await general_browser.new_context(
        viewport={"width": 390, "height": 844}
    )
    if incognito:
        await context.clear_cookies()
    await context.route("**/*", _adblock_router)

    async with session_lock:
        general_contexts[key] = {"context": context, "last_used": time.time()}
    return context

async def _adblock_router(route):
    url = route.request.url.lower()
    if any(ad in url for ad in AD_DOMAINS) or any(kw in url for kw in BLOCKED_AD_KEYWORDS):
        await route.abort()
    else:
        await route.continue_()

async def close_user_context(chat_id: int, incognito: bool = False):
    key = f"{chat_id}{'_incognito' if incognito else ''}"
    async with session_lock:
        if key in general_contexts:
            try:
                await general_contexts[key]["context"].close()
            except:
                pass
            del general_contexts[key]

async def cleanup_expired_contexts():
    while True:
        await asyncio.sleep(60)
        async with session_lock:
            now = time.time()
            expired_keys = [k for k, v in general_contexts.items() if now - v["last_used"] > 1200]
            for k in expired_keys:
                try:
                    await general_contexts[k]["context"].close()
                except:
                    pass
                del general_contexts[k]

        async with session_lock:
            for chat_id, session in list(sessions.items()):
                if session.browser_links and now - session.last_browser_time > 1200:
                    session.browser_links = None
                    session.browser_url = None
                    session.text_links = {}
                    session.browser_page = 0
                    session.last_browser_time = 0
                    async with callback_map_lock:
                        to_remove = [k for k in callback_map if k.startswith(f"nav_{chat_id}_") or k.startswith(f"dlvid_{chat_id}_")]
                        for k in to_remove:
                            del callback_map[k]

# ═══════════ Workerها ═══════════

async def general_worker():
    while True:
        job: Job = await general_queue.get()
        try:
            session = await get_session(job.chat_id)
            if session.cancel_requested:
                job.status = "cancelled"
                await update_job_status(job)
                session.cancel_requested = False
                await set_session(session)
                continue

            safe_log(f"Processing general job: {job.mode} ({job.job_id[:8]})")
            if job.mode in ("browser", "browser_click"):
                await process_browser_job(job)
            elif job.mode in ("screenshot", "2x_screenshot", "4k_screenshot"):
                await process_screenshot_job(job)
            elif job.mode in ("download", "download_execute", "blind_download", "download_website"):
                await process_download_job(job)
            elif job.mode in ("scan_downloads", "scan_videos", "extract_commands",
                              "smart_analyze", "source_analyze", "download_all_found"):
                await process_scan_job(job)
            elif job.mode == "captcha":
                await process_captcha_job(job)
            elif job.mode == "fullpage_screenshot":
                await process_fullpage_screenshot(job)
            elif job.mode == "interactive_scan":
                await process_interactive_scan(job)
            elif job.mode == "interactive_execute":
                await process_interactive_execute(job)
            elif job.mode == "wild_crawler":
                from K import start_crawl
                settings = job.extra.get("settings", {})
                stop_ev = asyncio.Event()
                async def crawler_progress(cid, msg):
                    if msg == "__FINAL_ZIP__":
                        pass  # handled separately
                    else:
                        await send_message(cid, msg)
                await start_crawl(job.chat_id, job.url, settings,
                                  progress_callback=crawler_progress,
                                  stop_event=stop_ev)
                job.status = "done"
            else:
                safe_log(f"Unknown job mode: {job.mode}")
        except Exception as e:
            safe_log(f"Job {job.job_id} error: {e}")
            traceback.print_exc()
            job.status = "error"
            await update_job_status(job)
        finally:
            general_queue.task_done()

async def record_worker():
    while True:
        job: Job = await record_queue.get()
        try:
            safe_log(f"Processing record job: {job.job_id[:8]}")
            await process_record_job(job)
        except Exception as e:
            safe_log(f"Record job {job.job_id} error: {e}")
            traceback.print_exc()
            job.status = "error"
            await update_job_status(job)
        finally:
            record_queue.task_done()

async def enqueue_job(job: Job):
    job.status = "queued"
    if job.queue_type == "record":
        await record_queue.put(job)
    else:
        await general_queue.put(job)

async def update_job_status(job: Job):
    job.updated_at = time.time()
    return job

# ═══════════ پردازش Job: مرورگر ═══════════

async def process_browser_job(job: Job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    url = job.url

    if is_direct_file_url(url):
        await send_message(chat_id, "📥 این لینک یک فایل مستقیم است. لطفاً از بخش دانلود استفاده کنید.")
        job.status = "done"
        return

    context = await get_user_context(chat_id, session.settings.incognito_mode)
    page = await context.new_page()

    job_dir = f"jobs/{job.job_id}"
    os.makedirs(job_dir, exist_ok=True)

    try:
        await page.goto(url, timeout=60000, wait_until="domcontentloaded")
        await page.wait_for_timeout(2000)

        spath = os.path.join(job_dir, "browser.png")
        await page.screenshot(path=spath, full_page=True)

        mode = session.settings.browser_mode
        links, video_urls = await extract_links_async(page, mode)

        all_links = []
        for typ, text, href in links:
            all_links.append({"type": typ, "text": text[:25], "href": href})
        if mode == "media":
            for vurl in video_urls:
                if not any(ad in vurl for ad in AD_DOMAINS):
                    all_links.append({"type": "video", "text": "🎬 ویدیو", "href": vurl})

        session.state = "browsing"
        session.browser_url = url
        session.browser_links = all_links
        session.browser_page = 0
        session.last_browser_time = time.time()
        await set_session(session)

        await send_browser_page(chat_id, spath, url, 0)
        job.status = "done"

    except Exception as e:
        await send_message(chat_id, f"❌ خطا در مرورگر: {e}")
        job.status = "error"
    finally:
        await page.close()
        shutil.rmtree(job_dir, ignore_errors=True)

async def extract_links_async(page, mode: str):
    if mode == "text":
        raw = await page.evaluate("""() => {
            const items = []; const seen = new Set();
            document.querySelectorAll('a[href]').forEach(a => {
                let t = a.textContent.trim() || 'لینک';
                try { var href = new URL(a.getAttribute('href'), document.baseURI).href; } catch(e) { return; }
                if (!seen.has(href)) { seen.add(href); items.push(['link', t, href]); }
            });
            return items;
        }""")
        links = [(t, txt, h) for t, txt, h in raw if h.startswith("http")]
        return links, []

    elif mode == "media":
        video_sources = await page.evaluate("""() => {
            const vids = [];
            document.querySelectorAll('video').forEach(v => {
                let src = v.src || (v.querySelector('source') ? v.querySelector('source').src : '');
                if (src) vids.push(src);
            });
            document.querySelectorAll('iframe').forEach(f => {
                if (f.src) vids.push(f.src);
            });
            return [...new Set(vids)].filter(u => u.startsWith('http'));
        }""")
        anchors = await page.evaluate("""() => {
            const a = []; document.querySelectorAll('a[href]').forEach(e => {
                try { a.push(new URL(e.getAttribute('href'), document.baseURI).href); } catch(e) {}
            });
            return a.filter(h => h && h.startsWith('http'));
        }""")
        links = [("link", href.split("/")[-1][:20] or "لینک", href) for href in anchors[:20]]
        return links, video_sources

    else:  # explorer
        raw = await page.evaluate("""() => {
            const items = []; const seen = new Set();
            function add(type, text, href) {
                if (!href || seen.has(href)) return;
                seen.add(href); items.push([type, text.trim().substring(0, 40), href]);
            }
            document.querySelectorAll('a[href]').forEach(a => {
                let t = a.textContent.trim() || 'لینک';
                try { var href = new URL(a.getAttribute('href'), document.baseURI).href; add('link', t, href); } catch(e) {}
            });
            document.querySelectorAll('button').forEach(btn => {
                let t = btn.textContent.trim() || 'دکمه';
                let formaction = btn.getAttribute('formaction') || '';
                if (formaction) { try { formaction = new URL(formaction, document.baseURI).href; } catch(e) {} add('button', t, formaction); }
            });
            return items;
        }""")
        links = [(t, txt, h) for t, txt, h in raw if h and (h.startswith("http") or h.startswith("/"))]
        return links, []

async def send_browser_page(chat_id, image_path=None, url="", page_num=0):
    session = await get_session(chat_id)
    all_links = session.browser_links or []
    per_page = 10
    start = page_num * per_page
    end = min(start + per_page, len(all_links))
    page_links = all_links[start:end]

    keyboard_rows = []
    idx = start
    row = []
    for link in page_links:
        label = link["text"][:20]
        cb = f"nav_{chat_id}_{idx}" if link["type"] != "video" else f"dlvid_{chat_id}_{idx}"
        async with callback_map_lock:
            callback_map[cb] = link["href"]
        row.append({"text": label, "callback_data": cb})
        if len(row) == 2:
            keyboard_rows.append(row)
            row = []
        idx += 1
    if row:
        keyboard_rows.append(row)

    nav = []
    if page_num > 0:
        nav.append({"text": "◀️", "callback_data": f"bpg_{chat_id}_{page_num-1}"})
    if end < len(all_links):
        nav.append({"text": "▶️", "callback_data": f"bpg_{chat_id}_{page_num+1}"})
    if nav:
        keyboard_rows.append(nav)

    sub = session.subscription
    mode = session.settings.browser_mode
    if mode == "media":
        if sub in ("plus", "pro") or session.is_admin:
            keyboard_rows.append([{"text": "🎬 اسکن ویدیوها", "callback_data": f"scvid_{chat_id}"}])
        parsed_url = urlparse(url)
        current_domain = parsed_url.netloc.lower()
        is_blocked = current_domain in (session.ad_blocked_domains or [])
        ad_text = "🛡️ تبلیغات: روشن" if is_blocked else "🛡️ تبلیغات: خاموش"
        keyboard_rows.append([{"text": ad_text, "callback_data": f"adblock_{chat_id}"}])
    elif mode == "explorer":
        if sub in ("plus", "pro") or session.is_admin:
            keyboard_rows.append([{"text": "🔍 تحلیل هوشمند", "callback_data": f"sman_{chat_id}"}])
            keyboard_rows.append([{"text": "🕵️ تحلیل سورس", "callback_data": f"srcan_{chat_id}"}])
    else:
        if sub in ("plus", "pro") or session.is_admin:
            keyboard_rows.append([{"text": "📦 جستجوی فایل‌ها", "callback_data": f"scdl_{chat_id}"}])

    keyboard_rows.append([{"text": "🪟 حل کپچا", "callback_data": f"captcha_{chat_id}"}])
    if sub in ("plus", "pro") or session.is_admin:
        keyboard_rows.append([{"text": "📋 فرامین", "callback_data": f"extcmd_{chat_id}"}])
        keyboard_rows.append([{"text": "🎬 ضبط", "callback_data": f"recvid_{chat_id}"}])
        keyboard_rows.append([{"text": "📸 شات کامل", "callback_data": f"fullshot_{chat_id}"}])
        keyboard_rows.append([{"text": "🔎 کاوشگر", "callback_data": f"intscan_{chat_id}"}])
    if sub in ("pro") or session.is_admin:
        keyboard_rows.append([{"text": "🌐 دانلود سایت", "callback_data": f"dlweb_{chat_id}"}])
    keyboard_rows.append([{"text": "❌ بستن", "callback_data": f"closebrowser_{chat_id}"}])

    kb = {"inline_keyboard": keyboard_rows}
    if image_path:
        await send_document(chat_id, image_path, caption=f"🌐 {url}")
    total_pages = math.ceil(len(all_links) / per_page)
    await send_message(chat_id, f"صفحه {page_num+1}/{total_pages}", reply_markup=kb)

    extra = all_links[end:]
    if extra:
        cmds = {}
        lines = ["🔹 لینک‌های بیشتر:"]
        for link in extra:
            cmd = f"/a{hashlib.md5(link['href'].encode()).hexdigest()[:5]}"
            cmds[cmd] = link['href']
            lines.append(f"{cmd} : {link['text']}")
        await send_message(chat_id, "\n".join(lines))
        session.text_links = {**session.text_links, **cmds}
        await set_session(session)

# ═══════════ پردازش Job: اسکرین‌شات ═══════════

async def process_screenshot_job(job: Job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    context = await get_user_context(chat_id, session.settings.incognito_mode)
    page = await context.new_page()
    job_dir = f"jobs/{job.job_id}"
    os.makedirs(job_dir, exist_ok=True)

    try:
        if job.mode == "screenshot":
            await send_message(chat_id, "📸 در حال اسکرین‌شات...")
            spath = os.path.join(job_dir, "screenshot.png")
            await page.goto(job.url, timeout=90000, wait_until="domcontentloaded")
            await page.wait_for_timeout(2000)
            await page.screenshot(path=spath, full_page=True)
            await send_document(chat_id, spath, caption="✅ اسکرین‌شات")
            if session.subscription in ("plus", "pro") or session.is_admin:
                kb = {"inline_keyboard": [[
                    {"text": "🔍 2x Zoom", "callback_data": f"req2x_{job.job_id}"},
                    {"text": "🖼️ 4K", "callback_data": f"req4k_{job.job_id}"}
                ]]}
                await send_message(chat_id, "کیفیت بالاتر:", reply_markup=kb)

        elif job.mode == "2x_screenshot":
            await send_message(chat_id, "🔍 2x Zoom...")
            spath = os.path.join(job_dir, "screenshot_2x.png")
            await page.goto(job.url, timeout=90000, wait_until="domcontentloaded")
            await page.wait_for_timeout(2000)
            await page.evaluate("document.body.style.zoom = '200%'")
            await page.wait_for_timeout(500)
            await page.screenshot(path=spath, full_page=True)
            await send_document(chat_id, spath, caption="✅ اسکرین‌شات 2x")

        elif job.mode == "4k_screenshot":
            await send_message(chat_id, "🖼️ 4K...")
            spath = os.path.join(job_dir, "screenshot_4k.png")
            await page.set_viewport_size({"width": 3840, "height": 2160})
            await page.goto(job.url, timeout=90000, wait_until="domcontentloaded")
            await page.wait_for_timeout(3000)
            await page.screenshot(path=spath, full_page=True)
            await send_document(chat_id, spath, caption="✅ اسکرین‌شات 4K")

        job.status = "done"

    except Exception as e:
        await send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"
    finally:
        await page.close()
        shutil.rmtree(job_dir, ignore_errors=True)
# ═══════════ پردازش Job: دانلود (store / stream / ADM) ═══════════

async def process_download_job(job: Job):
    chat_id = job.chat_id
    session = await get_session(chat_id)

    if job.mode == "download_website":
        await download_full_website_async(job)
        return

    url = job.url
    if not is_direct_file_url(url):
        await send_message(chat_id, "🔎 جستجوی لینک مستقیم...")
        direct_link = await async_crawl_for_download(url)
        if not direct_link:
            job.mode = "blind_download"
            await process_blind_download(job)
            return
    else:
        direct_link = url

    size_bytes = None
    try:
        async with aiohttp.ClientSession() as sess:
            async with sess.head(direct_link, timeout=10) as resp:
                if "Content-Length" in resp.headers:
                    size_bytes = int(resp.headers["Content-Length"])
    except:
        pass

    err = await check_rate_limit(chat_id, "download", size_bytes)
    if err:
        await send_message(chat_id, err)
        job.status = "cancelled"
        return

    fname = get_filename_from_url(direct_link)
    size_str = f"{size_bytes/1024/1024:.2f} MB" if size_bytes else "نامشخص"

    kb = {"inline_keyboard": [
        [{"text": "📦 ZIP", "callback_data": f"dlzip_{job.job_id}"},
         {"text": "📄 اصلی", "callback_data": f"dlraw_{job.job_id}"}],
        [{"text": "❌ لغو", "callback_data": f"canceljob_{job.job_id}"}]
    ]}
    await send_message(chat_id, f"📄 {fname} ({size_str})", reply_markup=kb)
    job.status = "awaiting_user"
    job.extra = {"direct_link": direct_link, "filename": fname}

async def execute_download_async(job: Job):
    chat_id = job.chat_id
    extra = job.extra
    session = await get_session(chat_id)
    mode = session.settings.default_download_mode
    pack_zip = extra.get("pack_zip", False)

    job_dir = f"jobs/{job.job_id}"
    os.makedirs(job_dir, exist_ok=True)

    if mode == "stream" and not pack_zip:
        await send_message(chat_id, "⚡ دانلود همزمان (stream)...")
        await async_stream_download(extra["direct_link"], extra["filename"], job_dir, chat_id)
        job.status = "done"
        shutil.rmtree(job_dir, ignore_errors=True)
        return

    if mode == "adm":
        await send_message(chat_id, "⚡⚡ دانلود ADM (چندبخشی + قابلیت ادامه)...")
        success = await async_adm_download(extra["direct_link"], extra["filename"], job_dir, chat_id)
        if not success:
            job.status = "error"
            shutil.rmtree(job_dir, ignore_errors=True)
            return
    else:
        # store
        fpath = os.path.join(job_dir, extra["filename"])
        await send_message(chat_id, "⏳ در حال دانلود...")
        async with aiohttp.ClientSession() as sess:
            async with sess.get(extra["direct_link"]) as resp:
                with open(fpath, "wb") as f:
                    async for chunk in resp.content.iter_chunked(8192):
                        f.write(chunk)

    # ارسال
    fpath = os.path.join(job_dir, extra["filename"])
    if pack_zip:
        parts = create_zip_and_split(fpath, extra["filename"])
        label = "ZIP"
    else:
        base, ext = os.path.splitext(extra["filename"])
        parts = split_file_binary(fpath, base, ext)
        label = "اصلی"

    for idx, p in enumerate(parts, 1):
        await send_document(chat_id, p, caption=f"{label} پارت {idx}/{len(parts)}")
    job.status = "done"
    shutil.rmtree(job_dir, ignore_errors=True)

async def async_adm_download(url: str, fname: str, job_dir: str, chat_id: int) -> bool:
    headers = {"User-Agent": "Mozilla/5.0"}
    segments = 9
    try:
        async with aiohttp.ClientSession() as sess:
            async with sess.head(url, headers=headers, timeout=10) as head:
                accept_ranges = head.headers.get("Accept-Ranges", "").lower() == "bytes"
                content_length = int(head.headers.get("Content-Length", 0))
                if not accept_ranges or content_length < segments * 1024:
                    await send_message(chat_id, "🔄 سرور از چندبخشی پشتیبانی نمی‌کند. دانلود تک‌اتصالی...")
                    fpath = os.path.join(job_dir, fname)
                    async with sess.get(url, headers=headers) as resp:
                        with open(fpath, "wb") as f:
                            async for chunk in resp.content.iter_chunked(8192):
                                f.write(chunk)
                    return True

            part_size = content_length // segments
            tasks = []
            for i in range(segments):
                start = i * part_size
                end = start + part_size - 1 if i < segments - 1 else content_length - 1
                tasks.append(_download_segment(url, job_dir, fname, start, end, headers))

            results = await asyncio.gather(*tasks, return_exceptions=True)
            for r in results:
                if isinstance(r, Exception):
                    raise r

            final_path = os.path.join(job_dir, fname)
            with open(final_path, "wb") as outfile:
                for i in range(segments):
                    seg_path = os.path.join(job_dir, f"{fname}.part{i}")
                    with open(seg_path, "rb") as infile:
                        outfile.write(infile.read())
                    os.remove(seg_path)
            await send_message(chat_id, f"✅ دانلود ADM کامل شد ({content_length/1024/1024:.1f}MB)")
            return True

    except Exception as e:
        await send_message(chat_id, f"❌ خطا در دانلود ADM: {e}")
        return False

async def _download_segment(url, job_dir, fname, start, end, headers):
    seg_path = os.path.join(job_dir, f"{fname}.part{start//max(1,(end-start))}")
    headers["Range"] = f"bytes={start}-{end}"
    async with aiohttp.ClientSession() as sess:
        async with sess.get(url, headers=headers) as resp:
            with open(seg_path, "wb") as f:
                async for chunk in resp.content.iter_chunked(8192):
                    f.write(chunk)

# ═══════════ ضبط ویدیو (مرورگر جداگانه) ═══════════

async def process_record_job(job: Job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    url = job.url
    rec_time = session.settings.record_time
    behavior = session.settings.record_behavior
    resolution = session.settings.video_resolution
    delivery = session.settings.video_delivery

    w, h = ALLOWED_RESOLUTIONS.get(resolution, (1280, 720))
    job_dir = f"jobs/{job.job_id}"
    os.makedirs(job_dir, exist_ok=True)

    await send_message(chat_id, f"🎬 ضبط {rec_time} ثانیه...")

    try:
        context = await record_browser.new_context(
            viewport={"width": w, "height": h},
            record_video_dir=job_dir,
            record_video_size={"width": w, "height": h}
        )
        page = await context.new_page()
        await page.goto(url, timeout=90000, wait_until="domcontentloaded")
        await page.wait_for_timeout(2000)

        if behavior == "scroll":
            await page.evaluate("window.scrollTo(0, document.body.scrollHeight)")
            await page.wait_for_timeout(rec_time * 1000)
        else:
            vx, vy = await _find_video_center(page)
            await page.mouse.click(vx, vy)
            await page.wait_for_timeout(rec_time * 1000)

        await page.close()
        video_path = await context.close()

        if not video_path or not os.path.exists(video_path):
            await send_message(chat_id, "❌ ویدیویی ضبط نشد.")
            job.status = "error"
            return

        use_zip = (delivery == "zip")
        if os.path.getsize(video_path) <= ZIP_PART_SIZE:
            if use_zip:
                zp = os.path.join(job_dir, "record.zip")
                with zipfile.ZipFile(zp, "w") as zf:
                    zf.write(video_path, "record.webm")
                await send_document(chat_id, zp, caption="🎬 ویدیو (ZIP)")
            else:
                await send_document(chat_id, video_path, caption="🎬 ویدیو")
        else:
            parts = split_file_binary(video_path, "record", ".webm") if not use_zip else create_zip_and_split(video_path, "record")
            for idx, p in enumerate(parts, 1):
                await send_document(chat_id, p, caption=f"پارت {idx}/{len(parts)}")

        job.status = "done"

    except Exception as e:
        await send_message(chat_id, f"❌ خطا در ضبط: {e}")
        job.status = "error"
    finally:
        shutil.rmtree(job_dir, ignore_errors=True)

async def _find_video_center(page):
    coords = await page.evaluate("""() => {
        const v = document.querySelector('video');
        if (v) { const r = v.getBoundingClientRect(); return {x: r.x+r.width/2, y: r.y+r.height/2}; }
        const f = document.querySelector('iframe');
        if (f) { const r = f.getBoundingClientRect(); return {x: r.x+r.width/2, y: r.y+r.height/2}; }
        return {x: window.innerWidth/2, y: window.innerHeight/2};
    }""")
    return coords["x"], coords["y"]

# ═══════════ پنل ادمین شیشه‌ای ═══════════

async def admin_panel(chat_id):
    kb = {"inline_keyboard": [
        [{"text": "➕ اضافه کردن کد", "callback_data": "admin_addcode"}],
        [{"text": "➖ حذف کد", "callback_data": "admin_listcodes"}],
        [{"text": "⛔ بن کاربر", "callback_data": "admin_ban"}],
        [{"text": "✅ رفع بن", "callback_data": "admin_unban"}],
        [{"text": "👥 کاربران", "callback_data": "admin_users"}],
        [{"text": "🔄 سرویس (فعال/غیرفعال)", "callback_data": "admin_toggleservice"}],
        [{"text": "💀 توقف همه", "callback_data": "admin_killall"}],
        [{"text": "🔙 بازگشت", "callback_data": "back_main"}]
    ]}
    await send_message(chat_id, "🛠️ پنل ادمین:", reply_markup=kb)

async def handle_admin_callback(chat_id, data, cq_id):
    if data == "admin_addcode":
        session = await get_session(chat_id)
        session.state = "admin_wait_code"
        await set_session(session)
        await send_message(chat_id, "📝 فرمت: `<سطح> <کد>`\nسطوح: free, bronze, plus, pro")
    elif data == "admin_toggleservice":
        global service_disabled
        service_disabled = not service_disabled
        status = "غیرفعال" if service_disabled else "فعال"
        await send_message(chat_id, f"🔄 سرویس {status} شد.")
    elif data == "admin_killall":
        for uid, s in sessions.items():
            s.cancel_requested = True
        await send_message(chat_id, "💀 درخواست توقف همه پردازش‌ها ثبت شد.")
    elif data == "admin_ban":
        session = await get_session(chat_id)
        session.state = "admin_wait_ban"
        await set_session(session)
        await send_message(chat_id, "⛔ فرمت: `<chat_id> <مدت به دقیقه (اختیاری)>`")
    elif data == "admin_unban":
        session = await get_session(chat_id)
        session.state = "admin_wait_unban"
        await set_session(session)
        await send_message(chat_id, "✅ فرمت: `<chat_id>`")
    elif data == "admin_users":
        users_list = "\n".join([f"🆔 {uid} – {s.subscription}" for uid, s in sessions.items()])
        await send_message(chat_id, f"👥 کاربران:\n{users_list or 'هیچ کاربری فعال نیست.'}")

# ═══════════ مدیریت پیام‌ها و callbackها ═══════════

async def handle_message(chat_id: int, text: str):
    session = await get_session(chat_id)

    if await is_banned(chat_id):
        await send_message(chat_id, "🚫 شما تحریم هستید.")
        return

    if service_disabled and not session.is_admin:
        await send_message(chat_id, "⛔ سرویس موقتاً غیرفعال است.")
        return

    # admin waiting states
    if session.is_admin and session.state.startswith("admin_wait_"):
        if session.state == "admin_wait_code":
            parts = text.split()
            if len(parts) == 2 and parts[0] in ("free", "bronze", "plus", "pro"):
                level, code = parts
                if await add_code(level, code):
                    await send_message(chat_id, f"✅ کد {code} به سطح {level} اضافه شد.")
                else:
                    await send_message(chat_id, "⛔ کد تکراری یا نامعتبر.")
            session.state = "idle"
            await set_session(session)
            return
        elif session.state == "admin_wait_ban":
            parts = text.split()
            try:
                target = int(parts[0])
                minutes = int(parts[1]) if len(parts) > 1 else None
                await ban_user(target, minutes)
                await send_message(chat_id, f"✅ کاربر {target} بن شد.")
            except:
                await send_message(chat_id, "❌ فرمت نادرست.")
            session.state = "idle"
            await set_session(session)
            return
        elif session.state == "admin_wait_unban":
            try:
                target = int(text.strip())
                if await unban_user(target):
                    await send_message(chat_id, f"✅ کاربر {target} از بن خارج شد.")
                else:
                    await send_message(chat_id, "⛔ کاربر بن نبوده.")
            except:
                await send_message(chat_id, "❌ chat_id نامعتبر.")
            session.state = "idle"
            await set_session(session)
            return

    # activation code
    if not session.is_admin and session.subscription == "free":
        level = await activate_code(chat_id, text)
        if level:
            session.subscription = level
            await set_session(session)
            await send_message(chat_id, f"✅ اشتراک {level} فعال شد!",
                               reply_markup=main_menu_keyboard(session.is_admin))
        else:
            await send_message(chat_id, "⛔ کد نامعتبر.")
        return

    # waiting for url
    if session.state.startswith("waiting_url_"):
        url = text.strip()
        if not url.startswith(("http://", "https://")):
            await send_message(chat_id, "❌ آدرس نامعتبر.")
            return
        mode_map = {
            "waiting_url_screenshot": "screenshot",
            "waiting_url_download": "download",
            "waiting_url_browser": "browser",
            "waiting_url_record": "record_video"
        }
        mode = mode_map.get(session.state)
        job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode=mode, url=url,
                  queue_type="record" if mode == "record_video" else "general")
        await enqueue_job(job)
        session.state = "idle"
        await set_session(session)
        await send_message(chat_id, "✅ در صف قرار گرفت.")
        return

    # crawler limit/time inputs
    if session.state == "waiting_crawler_limit":
        try:
            val = int(text)
            if val < 0: val = 0
            session.settings.crawler_limit = val
            session.state = "idle"
            await set_session(session)
            await send_message(chat_id, f"✅ محدودیت صفحات: {'خودکار' if val==0 else val}")
            kb = crawler_settings_keyboard(session.settings)
            await send_message(chat_id, "⚙️ تنظیمات خزنده:", reply_markup=kb)
        except:
            await send_message(chat_id, "❌ لطفاً یک عدد وارد کنید.")
        return

    if session.state == "waiting_crawler_time":
        try:
            val = int(text)
            val = max(5, min(30, val))
            session.settings.crawler_max_time = val
            session.state = "idle"
            await set_session(session)
            await send_message(chat_id, f"✅ زمان خزنده: {val} دقیقه")
            kb = crawler_settings_keyboard(session.settings)
            await send_message(chat_id, "⚙️ تنظیمات خزنده:", reply_markup=kb)
        except:
            await send_message(chat_id, "❌ لطفاً یک عدد وارد کنید.")
        return

    # crawler url confirmation
    if session.state == "waiting_crawler_url":
        url = text.strip()
        if not url.startswith(("http://", "https://")):
            await send_message(chat_id, "❌ آدرس نامعتبر.")
            return
        session.crawler_pending_url = url
        s = session.settings
        fil = s.crawler_filters
        active = [k for k, v in fil.items() if v]
        summary = (
            f"⚙️ **تنظیمات خزنده:**\n"
            f"حالت: {s.crawler_mode} | لایه‌ها: {s.crawler_layers} | "
            f"صفحات: {'خودکار' if s.crawler_limit==0 else s.crawler_limit}\n"
            f"زمان: {s.crawler_max_time}m | ضدتبلیغ: {'✅' if s.crawler_adblock else '❌'}\n"
            f"Sitemap: {'✅' if s.crawler_sitemap else '❌'} | اولویت: {'✅' if s.crawler_priority else '❌'} | "
            f"JS: {'✅' if s.crawler_js else '❌'}\n"
            f"فیلترها: {', '.join(active) if active else 'همه'}\n\n"
            f"🌐 آدرس: {url}\nآیا شروع شود؟"
        )
        kb = {"inline_keyboard": [
            [{"text": "✅ شروع", "callback_data": "crawler_confirm_yes"},
             {"text": "❌ لغو", "callback_data": "crawler_confirm_no"}]
        ]}
        await send_message(chat_id, summary, reply_markup=kb)
        session.state = "idle"
        await set_session(session)
        return

    # /start and /cancel
    if text == "/start":
        session.state = "idle"
        await set_session(session)
        await send_message(chat_id, "منوی اصلی:", reply_markup=main_menu_keyboard(session.is_admin))
    elif text == "/cancel":
        session.cancel_requested = True
        await set_session(session)
        await send_message(chat_id, "⏹️ درخواست لغو ثبت شد. فرایندها به‌زودی متوقف می‌شوند.")
    elif session.state == "browsing" and text in session.text_links:
        url = session.text_links.pop(text)
        await set_session(session)
        job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="browser", url=url)
        await enqueue_job(job)
    else:
        await send_message(chat_id, "از منو استفاده کنید:", reply_markup=main_menu_keyboard(session.is_admin))

async def handle_callback(cq: dict):
    cid = cq["id"]
    msg = cq.get("message")
    data = cq.get("data", "")
    if not msg:
        return await answer_callback_query(cid)
    chat_id = msg["chat"]["id"]
    session = await get_session(chat_id)

    # main menu
    if data == "menu_browser":
        session.state = "waiting_url_browser"
        await set_session(session)
        await send_message(chat_id, "🧭 لینک صفحه:")
    elif data == "menu_screenshot":
        session.state = "waiting_url_screenshot"
        await set_session(session)
        await send_message(chat_id, "📸 لینک صفحه:")
    elif data == "menu_download":
        session.state = "waiting_url_download"
        await set_session(session)
        await send_message(chat_id, "📥 لینک:")
    elif data == "menu_record":
        session.state = "waiting_url_record"
        await set_session(session)
        await send_message(chat_id, "🎬 لینک ویدیو:")
    elif data == "menu_settings":
        kb = settings_keyboard(session.settings, session.subscription)
        msg = await send_message(chat_id, "⚙️ تنظیمات:", reply_markup=kb)
        if msg and "message_id" in msg:
            session.last_settings_msg_id = str(msg["message_id"])
            await set_session(session)
    elif data == "menu_admin":
        if session.is_admin:
            await admin_panel(chat_id)
        else:
            await answer_callback_query(cid, "⛔ دسترسی غیرمجاز")
    elif data.startswith("admin_"):
        await handle_admin_callback(chat_id, data, cid)

    # crawler menu and settings
    elif data == "menu_crawler":
        kb = crawler_settings_keyboard(session.settings)
        msg = await send_message(chat_id, "🕸️ تنظیمات خزنده وحشی:", reply_markup=kb)
        if msg and "message_id" in msg:
            session.last_crawler_msg_id = str(msg["message_id"])
            await set_session(session)
    elif data == "crawler_mode":
        modes = ["normal", "medium", "deep"]
        idx = modes.index(session.settings.crawler_mode)
        session.settings.crawler_mode = modes[(idx+1)%3]
        await set_session(session)
        await answer_callback_query(cid, f"✅ حالت: {session.settings.crawler_mode}")
        await _refresh_crawler_settings(chat_id, session)
    elif data == "crawler_layers":
        session.settings.crawler_layers = (session.settings.crawler_layers % 3) + 1
        await set_session(session)
        await answer_callback_query(cid, f"✅ لایه‌ها: {session.settings.crawler_layers}")
        await _refresh_crawler_settings(chat_id, session)
    elif data == "crawler_limit":
        session.state = "waiting_crawler_limit"
        await set_session(session)
        await send_message(chat_id, "📄 تعداد صفحات (0 = خودکار):")
    elif data == "crawler_time":
        session.state = "waiting_crawler_time"
        await set_session(session)
        await send_message(chat_id, "⏱️ زمان (دقیقه، ۵ تا ۳۰):")
    elif data.startswith("crawler_filter_"):
        filt = data.split("_")[-1]
        session.settings.crawler_filters[filt] = not session.settings.crawler_filters[filt]
        await set_session(session)
        await answer_callback_query(cid, "✅ تغییر یافت")
        await _refresh_crawler_settings(chat_id, session)
    elif data in ("crawler_adblock", "crawler_sitemap", "crawler_priority", "crawler_js"):
        attr = {
            "crawler_adblock": "crawler_adblock",
            "crawler_sitemap": "crawler_sitemap",
            "crawler_priority": "crawler_priority",
            "crawler_js": "crawler_js"
        }[data]
        setattr(session.settings, attr, not getattr(session.settings, attr))
        await set_session(session)
        await answer_callback_query(cid, "✅ تغییر یافت")
        await _refresh_crawler_settings(chat_id, session)
    elif data == "crawler_start":
        session.state = "waiting_crawler_url"
        await set_session(session)
        await send_message(chat_id, "🔗 لینک شروع خزنده را بفرستید:")
    elif data == "crawler_confirm_yes":
        url = session.crawler_pending_url
        if not url:
            await answer_callback_query(cid, "آدرس موجود نیست.")
            return
        job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="wild_crawler", url=url, queue_type="general")
        job.extra = {"settings": {
            "mode": session.settings.crawler_mode,
            "layers": session.settings.crawler_layers,
            "max_pages": session.settings.crawler_limit,
            "max_time_minutes": session.settings.crawler_max_time,
            "file_filters": session.settings.crawler_filters,
            "adblock": session.settings.crawler_adblock,
            "use_sitemap": session.settings.crawler_sitemap,
            "priority": session.settings.crawler_priority,
            "js_mode": session.settings.crawler_js
        }}
        await enqueue_job(job)
        await send_message(chat_id, "✅ خزنده در صف قرار گرفت. منتظر پیام‌های پیشرفت باشید.")
    elif data == "crawler_confirm_no":
        await send_message(chat_id, "❌ خزنده لغو شد.", reply_markup=main_menu_keyboard(session.is_admin))

    # settings toggles
    elif data == "set_dlmode":
        modes = ["store", "stream", "adm"]
        cur = session.settings.default_download_mode
        session.settings.default_download_mode = modes[(modes.index(cur)+1)%3]
        await set_session(session)
        await answer_callback_query(cid, f"✅ دانلود: {session.settings.default_download_mode}")
        await _refresh_settings(chat_id, session)
    elif data == "set_brwmode":
        modes = ["text", "media", "explorer"]
        cur = session.settings.browser_mode
        session.settings.browser_mode = modes[(modes.index(cur)+1)%3]
        await set_session(session)
        await answer_callback_query(cid, f"✅ حالت: {session.settings.browser_mode}")
        await _refresh_settings(chat_id, session)
    elif data == "set_deep":
        session.settings.deep_scan_mode = "everything" if session.settings.deep_scan_mode == "logical" else "logical"
        await set_session(session)
        await answer_callback_query(cid, "✅ تغییر یافت")
        await _refresh_settings(chat_id, session)
    elif data == "set_recbeh":
        behaviors = ["click", "scroll"]
        cur = session.settings.record_behavior
        session.settings.record_behavior = behaviors[(behaviors.index(cur)+1)%2]
        await set_session(session)
        await answer_callback_query(cid, f"✅ رفتار: {session.settings.record_behavior}")
        await _refresh_settings(chat_id, session)
    elif data == "set_audio":
        session.settings.audio_enabled = not session.settings.audio_enabled
        await set_session(session)
        await answer_callback_query(cid, "✅ تغییر یافت")
        await _refresh_settings(chat_id, session)
    elif data == "set_vfmt":
        formats = ["webm", "mkv", "mp4"]
        cur = session.settings.video_format
        session.settings.video_format = formats[(formats.index(cur)+1)%3]
        await set_session(session)
        await answer_callback_query(cid, f"✅ فرمت: {session.settings.video_format}")
        await _refresh_settings(chat_id, session)
    elif data == "set_incognito":
        session.settings.incognito_mode = not session.settings.incognito_mode
        await set_session(session)
        await answer_callback_query(cid, "✅ تغییر یافت")
        await _refresh_settings(chat_id, session)
    elif data == "set_viddel":
        session.settings.video_delivery = "zip" if session.settings.video_delivery == "split" else "split"
        await set_session(session)
        await answer_callback_query(cid, "✅ تغییر یافت")
        await _refresh_settings(chat_id, session)
    elif data == "set_resolution":
        resolutions = ["480p", "720p", "1080p", "4k"]
        cur = session.settings.video_resolution
        session.settings.video_resolution = resolutions[(resolutions.index(cur)+1)%4]
        await set_session(session)
        await answer_callback_query(cid, f"✅ کیفیت: {session.settings.video_resolution}")
        await _refresh_settings(chat_id, session)

    # navigation in browser
    elif data.startswith("nav_") or data.startswith("dlvid_"):
        async with callback_map_lock:
            url = callback_map.pop(data, None)
        if url:
            job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="browser", url=url)
            await enqueue_job(job)

    elif data.startswith("bpg_"):
        parts = data.split("_")
        if len(parts) == 3:
            page = int(parts[2])
            session.browser_page = page
            await set_session(session)
            await send_browser_page(chat_id, page_num=page)

    elif data.startswith("closebrowser_"):
        session.browser_links = None
        session.browser_url = None
        session.state = "idle"
        await set_session(session)
        await send_message(chat_id, "🧭 بسته شد.", reply_markup=main_menu_keyboard(session.is_admin))

    elif data == "back_main":
        await send_message(chat_id, "منوی اصلی:", reply_markup=main_menu_keyboard(session.is_admin))

    else:
        await answer_callback_query(cid)

async def _refresh_settings(chat_id, session):
    if session.last_settings_msg_id:
        kb = settings_keyboard(session.settings, session.subscription)
        await edit_message_reply_markup(chat_id, session.last_settings_msg_id, kb)

async def _refresh_crawler_settings(chat_id, session):
    if session.last_crawler_msg_id:
        kb = crawler_settings_keyboard(session.settings)
        await edit_message_reply_markup(chat_id, session.last_crawler_msg_id, kb)

# ═══════════ Polling و Main ═══════════

async def polling_loop():
    offset = None
    while True:
        try:
            updates = await get_updates(offset)
            for upd in updates:
                offset = upd["update_id"] + 1
                if "message" in upd and "text" in upd["message"]:
                    asyncio.create_task(handle_message(upd["message"]["chat"]["id"], upd["message"]["text"]))
                elif "callback_query" in upd:
                    asyncio.create_task(handle_callback(upd["callback_query"]))
        except Exception as e:
            safe_log(f"Poll error: {e}")
            await asyncio.sleep(5)

async def main():
    await load_subscriptions()
    await init_browsers()

    for _ in range(3):
        asyncio.create_task(general_worker())
    asyncio.create_task(record_worker())

    asyncio.create_task(cleanup_expired_contexts())

    asyncio.create_task(polling_loop())

    safe_log("✅ Bot اجرا شد")
    await asyncio.Future()

if __name__ == "__main__":
    asyncio.run(main())
