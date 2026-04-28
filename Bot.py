#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
بات نهایی - نسخه کامل Async + PulseAudio + Wild Crawler
رفع تمام باگ‌ها، بدون تکه‌تکه‌شدن کد.
"""

import os, sys, json, time, math, uuid, re, hashlib, zipfile, shutil
import asyncio, subprocess, traceback, io, csv
from dataclasses import dataclass, asdict, field
from typing import Dict, Any, Optional, List, Tuple, Set
from urllib.parse import urlparse, urljoin, unquote

import aiohttp
from bs4 import BeautifulSoup
from playwright.async_api import async_playwright

# ═══════════ تنظیمات ثابت ═══════════
BOT_TOKEN = os.getenv("BALE_BOT_TOKEN", "").strip()
if not BOT_TOKEN:
    print("FATAL: BALE_BOT_TOKEN not set", file=sys.stderr)
    sys.exit(1)

API_BASE = f"https://tapi.bale.ai/bot{BOT_TOKEN}"
REQUEST_TIMEOUT = aiohttp.ClientTimeout(total=30)
ZIP_PART_SIZE = 19 * 1024 * 1024
DATA_DIR = "data"
os.makedirs(DATA_DIR, exist_ok=True)
SUBSCRIPTIONS_FILE = os.path.join(DATA_DIR, "subscriptions.json")
ADMIN_CHAT_ID = 46829437

PLAN_LIMITS = {
    "free": {
        "browser": (2, 3600, None), "screenshot": (2, 3600, None),
        "2x_screenshot": (0, 3600, None), "4k_screenshot": (0, 3600, None),
        "download": (1, 3600, 10*1024*1024), "record_video": (0, 3600, None),
        "scan_downloads": (0, 3600, None), "scan_videos": (0, 3600, None),
        "download_website": (0, 3600, None), "extract_commands": (0, 3600, None),
    },
    "bronze": {
        "browser": (5, 3600, None), "screenshot": (2, 3600, None),
        "2x_screenshot": (1, 3600, None), "4k_screenshot": (1, 3600, None),
        "download": (2, 3600, 100*1024*1024), "record_video": (1, 3600, None),
        "scan_downloads": (1, 3600, None), "scan_videos": (1, 3600, None),
        "download_website": (0, 3600, None), "extract_commands": (1, 3600, None),
    },
    "plus": {
        "browser": (10, 3600, None), "screenshot": (10, 3600, None),
        "2x_screenshot": (5, 3600, None), "4k_screenshot": (3, 3600, None),
        "download": (5, 3600, 600*1024*1024), "record_video": (3, 3600, None),
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

HARDCODED_CODES = {
    "bronze": ["BR001","BR002","BR003","BR004","BR005"],
    "plus":   ["PL001","PL002","PL003","PL004","PL005"],
    "pro":    ["PR001","PR002","PR003","PR004","PR005"],
}

# ═══════════ قفل‌های asyncio ═══════════
session_lock = asyncio.Lock()
sub_lock = asyncio.Lock()
job_lock = asyncio.Lock()
callback_map_lock = asyncio.Lock()

# ═══════════ وضعیت کلی ═══════════
subscriptions_data = None
service_disabled = False

general_queue = asyncio.Queue()
record_queue = asyncio.Queue()

general_playwright = None
general_browser = None
general_contexts: Dict[str, Any] = {}

record_playwright = None
record_browser = None

active_jobs: Dict[str, "Job"] = {}
job_store: List[Dict[str, Any]] = []
callback_map: Dict[str, str] = {}

# ═══════════ مدل‌های داده ═══════════
@dataclass
class UserSettings:
    record_time: int = 20
    default_download_mode: str = "store"     # store / stream / adm
    browser_mode: str = "text"               # text / media / explorer
    deep_scan_mode: str = "logical"
    record_behavior: str = "click"           # click / scroll / live
    audio_enabled: bool = False
    video_format: str = "webm"
    incognito_mode: bool = False
    video_delivery: str = "split"            # split / zip
    video_resolution: str = "720p"
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

# ═══════════ توابع کمکی ═══════════
async def safe_log(msg: str):
    try:
        loop = asyncio.get_running_loop()
        await loop.run_in_executor(None, _sync_log, msg)
    except:
        pass

def _sync_log(msg: str):
    with open("bot.log", "a", encoding="utf-8") as f:
        f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} {msg}\n")
    print(msg, flush=True)

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
    with open(file_path, "rb") as f:
        i = 1
        while True:
            chunk = f.read(ZIP_PART_SIZE)
            if not chunk:
                break
            pname = f"{prefix}.part{i:03d}{ext}" if ext.lower() != ".zip" else f"{prefix}.zip.{i:03d}"
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
    with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as zf:
        zf.write(src, os.path.basename(src))
    if os.path.getsize(zp) <= ZIP_PART_SIZE:
        return [zp]
    parts = split_file_binary(zp, base, ".zip")
    os.remove(zp)
    return parts

# ═══════════ مدیریت اشتراک و Git ═══════════
async def load_subscriptions() -> dict:
    global subscriptions_data
    data = {}
    if os.path.exists(SUBSCRIPTIONS_FILE):
        try:
            with open(SUBSCRIPTIONS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
        except:
            pass
    if not data:
        data = {"valid_codes": HARDCODED_CODES.copy(), "user_levels": {}, "bans": {}}
        async with sub_lock:
            with open(SUBSCRIPTIONS_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
    subscriptions_data = data
    return data

async def save_subscriptions(data: dict = None):
    global subscriptions_data
    if data is None:
        data = subscriptions_data
    if data is None:
        return
    async with sub_lock:
        with open(SUBSCRIPTIONS_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        subscriptions_data = data
    asyncio.create_task(git_commit_and_push(SUBSCRIPTIONS_FILE))

async def git_commit_and_push(filepath: str, message: str = "auto: update subscriptions"):
    if not os.getenv("GITHUB_TOKEN"):
        return
    try:
        repo = os.getenv("GITHUB_REPOSITORY", "")
        token = os.getenv("GITHUB_TOKEN", "")
        if not repo or not token:
            return
        cmds = [
            ["git", "config", "user.name", "bot"],
            ["git", "config", "user.email", "bot@no-reply.com"],
            ["git", "add", filepath],
            ["git", "commit", "-m", message],
            ["git", "push", f"https://x-access-token:{token}@github.com/{repo}.git", "HEAD:main"]
        ]
        for cmd in cmds:
            proc = await asyncio.create_subprocess_exec(
                *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
            )
            await proc.communicate()
        await safe_log(f"Git pushed: {filepath}")
    except Exception as e:
        await safe_log(f"Git push failed: {e}")

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
    await save_subscriptions()
    return True

async def remove_code(code: str) -> Optional[str]:
    data = await load_subscriptions()
    codes = data.get("valid_codes", {})
    for level, codelist in codes.items():
        if code in codelist:
            codelist.remove(code)
            await save_subscriptions()
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
        await save_subscriptions()
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

# ═══════════ محدودیت مصرف ═══════════
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
sessions: Dict[int, "SessionState"] = {}

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

# ═══════════ مدیریت Job ═══════════
async def enqueue_job(job: Job):
    job.status = "queued"
    async with job_lock:
        active_jobs[job.job_id] = job
        job_store.append(asdict(job))
    if job.queue_type == "record":
        await record_queue.put(job)
    else:
        await general_queue.put(job)

async def find_job(job_id: str) -> Optional[Job]:
    async with job_lock:
        return active_jobs.get(job_id)

async def update_job_status(job: Job):
    async with job_lock:
        if job.job_id in active_jobs:
            active_jobs[job.job_id] = job
            for item in job_store:
                if item["job_id"] == job.job_id:
                    item.update(asdict(job))
                    break

# ═══════════ API بله ═══════════
async def bale_request(method: str, params: dict = None, files: dict = None) -> Optional[dict]:
    url = f"{API_BASE}/{method}"
    async with aiohttp.ClientSession(timeout=REQUEST_TIMEOUT) as sess:
        try:
            if files:
                data = aiohttp.FormData()
                for k, v in (params or {}).items():
                    data.add_field(k, str(v))
                for k, v in files.items():
                    data.add_field(k, v[1], filename=v[0])
                async with sess.post(url, data=data) as resp:
                    if resp.status == 200:
                        j = await resp.json()
                        if j.get("ok"):
                            return j["result"]
            else:
                async with sess.post(url, json=params or {}) as resp:
                    if resp.status == 200:
                        j = await resp.json()
                        if j.get("ok"):
                            return j["result"]
        except Exception as e:
            await safe_log(f"API {method} error: {e}")
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

# ═══════════ منوها ═══════════
def main_menu_keyboard(is_admin=False, subscription="free"):
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
    rec_behavior = {"click": "🖱️ کلیک", "scroll": "📜 اسکرول", "live": "🎭 لایو"}[settings.record_behavior]
    audio = "🔊 با صدا" if settings.audio_enabled else "🔇 بی‌صدا"
    vfmt = settings.video_format.upper()
    incognito = "🕶️ ناشناس" if settings.incognito_mode else "👤 عادی"
    delivery = "ZIP 📦" if settings.video_delivery == "zip" else "تکه‌ای 🧩"
    res = settings.video_resolution
    kb = [
        [{"text": f"⏱️ زمان: {rec}s", "callback_data": "set_rec"}],
        [{"text": f"📥 دانلود: {dlm}", "callback_data": "set_dlmode"}],
        [{"text": f"🌐 حالت: {mode}", "callback_data": "set_brwmode"}],
        [{"text": f"🔍 جستجو: {deep}", "callback_data": "set_deep"}],
        [{"text": f"🎬 ضبط: {rec_behavior}", "callback_data": "set_recbeh"}],
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

# ═══════════ راه‌اندازی مرورگرها ═══════════
async def init_browsers():
    global general_playwright, general_browser, record_playwright, record_browser
    await safe_log("Launching general browser...")
    general_playwright = await async_playwright().start()
    general_browser = await general_playwright.chromium.launch(
        headless=True,
        args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu",
              "--autoplay-policy=no-user-gesture-required"]
    )
    await safe_log("Launching record browser...")
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
            # پاکسازی contextهای منقضی‌شده
            expired = [k for k, v in general_contexts.items() if now - v["last_used"] > 1200]
            for k in expired:
                try:
                    await general_contexts[k]["context"].close()
                except:
                    pass
                del general_contexts[k]
            # پاکسازی sessionهای قدیمی (همه داخل یک قفل)
            for cid, s in list(sessions.items()):
                if s.browser_links and now - s.last_browser_time > 1200:
                    s.browser_links = None
                    s.browser_url = None
                    s.text_links = {}
                    s.browser_page = 0
                    s.last_browser_time = 0
                    async with callback_map_lock:
                        to_remove = [k for k in callback_map if k.startswith(f"nav_{cid}_") or k.startswith(f"dlvid_{cid}_")]
                        for k in to_remove:
                            del callback_map[k]
                if s.browser_links and now - s.last_browser_time > 1200:
                    s.browser_links = None
                    s.browser_url = None
                    s.text_links = {}
                    s.browser_page = 0
                    s.last_browser_time = 0
                    async with callback_map_lock:
                        to_remove = [k for k in callback_map if k.startswith(f"nav_{cid}_") or k.startswith(f"dlvid_{cid}_")]
                        for k in to_remove:
                            del callback_map[k]

# ═══════════ سیستم صدا (PulseAudio) - بازنویسی async ═══════════
async def setup_pulseaudio_async() -> bool:
    """راه‌اندازی PulseAudio و ایجاد null-sink"""
    try:
        if shutil.which("pulseaudio") is None:
            proc = await asyncio.create_subprocess_exec(
                "apt-get", "update", "-qq",
                stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
            )
            await proc.communicate()
            proc = await asyncio.create_subprocess_exec(
                "apt-get", "install", "-y", "-qq", "pulseaudio",
                stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
            )
            await proc.communicate()
        proc = await asyncio.create_subprocess_exec(
            "pulseaudio", "--start",
            stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
        )
        await proc.communicate()
        await asyncio.sleep(1)
        proc = await asyncio.create_subprocess_exec(
            "pactl", "load-module", "module-null-sink", "sink_name=virtual_out",
            "sink_properties=device.description=Virtual_Output",
            stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
        )
        stdout, stderr = await proc.communicate()
        if proc.returncode == 0:
            os.environ["PULSE_SINK"] = "virtual_out"
            await safe_log("PulseAudio null-sink virtual_out loaded")
            return True
        else:
            os.environ["PULSE_SINK"] = "virtual_out"
            return True
    except Exception as e:
        await safe_log(f"PulseAudio setup failed: {e}")
        return False

async def start_audio_capture_async(job_dir: str) -> Tuple[Optional[asyncio.subprocess.Process], str]:
    audio_path = os.path.join(job_dir, "audio.mp3")
    if not shutil.which("ffmpeg"):
        return None, audio_path
    cmd = [
        'ffmpeg', '-y',
        '-f', 'pulse', '-i', 'virtual_out.monitor',
        '-ac', '2', '-ar', '44100',
        '-acodec', 'libmp3lame', '-b:a', '128k',
        audio_path
    ]
    try:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        await safe_log(f"started ffmpeg pulse capture to {audio_path}")
        return proc, audio_path
    except Exception as e:
        await safe_log(f"start_audio_capture_async failed: {e}")
        return None, audio_path

async def stop_audio_capture_async(proc: Optional[asyncio.subprocess.Process], audio_path: str) -> bool:
    if not proc:
        return False
    try:
        proc.terminate()
        await proc.wait()
        size = os.path.getsize(audio_path) if os.path.exists(audio_path) else 0
        await safe_log(f"audio capture stopped, size={size} bytes")
        return size > 0
    except Exception as e:
        await safe_log(f"stop_audio_capture_async error: {e}")
        return False

# ═══════════ Workerها (اسکلت - توابع اصلی پردازش job در پارت ۲) ═══════════
async def general_worker():
    while True:
        job: Job = await general_queue.get()
        try:
            session = await get_session(job.chat_id)
            if session.cancel_requested:
                session.cancel_requested = False
                await set_session(session)
                job.status = "cancelled"
                await update_job_status(job)
                continue

            await safe_log(f"Processing general job: {job.mode} ({job.job_id[:8]})")
            if job.mode in ("browser", "browser_click"):
                await process_browser_job(job)
            elif job.mode in ("screenshot", "2x_screenshot", "4k_screenshot"):
                await process_screenshot_job(job)
            elif job.mode == "record_video":
                await process_record_job(job)
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

                # ★ callback خزنده (فایل نهایی را چک کرده و در صورت لزوم تقسیم می‌کند)
                async def crawler_progress(cid, msg, file_path=None):
                    if msg == "__FINAL_ZIP__":
                        if file_path and os.path.exists(file_path):
                            size = os.path.getsize(file_path)
                            if size <= ZIP_PART_SIZE:
                                await send_document(cid, file_path, caption="🕸️ نتیجه خزنده وحشی")
                            else:
                                parts = split_file_binary(file_path, "crawler_result", ".zip")
                                for idx, p in enumerate(parts, 1):
                                    await send_document(cid, p, caption=f"🕸️ نتیجه خزنده (پارت {idx}/{len(parts)})")
                        else:
                            await send_message(cid, "❌ فایل خروجی خزنده یافت نشد.")
                    else:
                        await send_message(cid, msg)

                await start_crawl(job.chat_id, job.url, settings,
                                  progress_callback=crawler_progress,
                                  stop_event=stop_ev)
                job.status = "done"
                await update_job_status(job)
            else:
                await safe_log(f"Unknown job mode: {job.mode}")
        except Exception as e:
            await safe_log(f"Job {job.job_id} error: {e}")
            traceback.print_exc()
            job.status = "error"
            await update_job_status(job)
        finally:
            general_queue.task_done()

async def record_worker():
    while True:
        job: Job = await record_queue.get()
        try:
            await safe_log(f"Processing record job: {job.job_id[:8]}")
            await process_record_job(job)
        except Exception as e:
            await safe_log(f"Record job {job.job_id} error: {e}")
            traceback.print_exc()
            job.status = "error"
            await update_job_status(job)
        finally:
            record_queue.task_done()

# ═══════════ ادامه در پارت ۲ ═══════════
# پارت ۲ شامل این توابع خواهد بود (همه با پیاده‌سازی کامل):
#   process_browser_job, send_browser_page
#   extract_links_async, scan_videos_smart, smooth_scroll_to_video, _find_video_center
#   process_screenshot_job
#   process_record_job
#   async_crawl_for_download, process_download_job, process_blind_download
#   async_stream_download, async_adm_download, _download_segment
#   download_full_website_async, _finish_website_download
#   execute_download_async
#   process_scan_job و همه زیرتابع‌هایش (handle_scan_downloads, send_found_downloads_page,
#     handle_scan_videos, handle_extract_commands, handle_smart_analyze,
#     handle_source_analyze, handle_download_all_found)
#   process_captcha_job
#   process_fullpage_screenshot
#   process_interactive_scan, process_interactive_execute
#   handle_callback (اصلی)
#   handle_other_callbacks (یکبار و کامل شامل تمام شاخه‌ها)
#   handle_admin_callback, admin_panel
#   handle_message, handle_live_command
#   _refresh_settings, _refresh_crawler_settings
#   polling_loop, main
#
# همچنین K.py اصلاح‌شده (با تأخیر دامنه و بستن CSV و callback سه‌آرگومانه) جداگانه ارائه خواهد شد.
# در این پارت هیچ تابعی از پارت ۲ تعریف نشده تا از هم‌پوشانی جلوگیری شود.

# ═══════════════════════ توابع استخراج لینک، ویدیو، اسکرول ═══════════════════════
async def extract_links_async(page, mode: str):
    """استخراج لینک‌ها بر اساس حالت مرورگر (text/media/explorer)"""
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

async def scan_videos_smart(page):
    """اسکن هوشمند ویدیوها (عناصر + شبکه + اسکریپت‌ها)"""
    elements = await page.evaluate("""() => {
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
    await page.wait_for_timeout(3000)
    try:
        page.remove_listener("response", capture)
    except:
        pass

    json_urls = await page.evaluate("""() => {
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
        if not href.startswith("http"): continue
        parsed = urlparse(href)
        if any(ad in parsed.netloc for ad in AD_DOMAINS): continue
        if any(kw in href.lower() for kw in BLOCKED_AD_KEYWORDS): continue
        all_candidates.append({"text": (el["text"] + f" ({parsed.netloc})")[:35], "href": href, "score": el["score"]})
    for url in network_urls:
        if url in [c["href"] for c in all_candidates]: continue
        parsed = urlparse(url)
        if any(ad in parsed.netloc for ad in AD_DOMAINS): continue
        all_candidates.append({"text": f"Network stream ({parsed.netloc})"[:35], "href": url, "score": 100000})
    for url in json_urls:
        if url in [c["href"] for c in all_candidates]: continue
        parsed = urlparse(url)
        if any(ad in parsed.netloc for ad in AD_DOMAINS): continue
        all_candidates.append({"text": f"JSON stream ({parsed.netloc})"[:35], "href": url, "score": 90000})
    all_candidates.sort(key=lambda x: x["score"], reverse=True)
    return all_candidates

async def smooth_scroll_to_video(page):
    coords = await page.evaluate("""() => {
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
    current_y = await page.evaluate("window.scrollY")
    distance = target_y - current_y
    steps = max(20, abs(distance) // 15)
    step_size = distance / steps
    for _ in range(steps):
        current_y += step_size
        await page.evaluate(f"window.scrollTo({{top: {int(current_y)}, behavior: 'smooth'}})")
        await page.wait_for_timeout(50)
    await page.evaluate(f"window.scrollTo({{top: {int(target_y)}, behavior: 'smooth'}})")
    await page.wait_for_timeout(200)

async def _find_video_center(page):
    coords = await page.evaluate("""() => {
        const v = document.querySelector('video');
        if (v) { const r = v.getBoundingClientRect(); return {x: r.x+r.width/2, y: r.y+r.height/2}; }
        const f = document.querySelector('iframe');
        if (f) { const r = f.getBoundingClientRect(); return {x: r.x+r.width/2, y: r.y+r.height/2}; }
        return {x: window.innerWidth/2, y: window.innerHeight/2};
    }""")
    return coords["x"], coords["y"]

# ═══════════ پردازش مرورگر ═══════════
async def process_browser_job(job: Job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    url = job.url
    if is_direct_file_url(url):
        await send_message(chat_id, "📥 این لینک یک فایل مستقیم است. لطفاً از بخش دانلود استفاده کنید.")
        job.status = "done"
        await update_job_status(job)
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
        await update_job_status(job)
    except Exception as e:
        await send_message(chat_id, f"❌ خطا در مرورگر: {e}")
        job.status = "error"
        await update_job_status(job)
    finally:
        await page.close()
        shutil.rmtree(job_dir, ignore_errors=True)

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

# ═══════════ اسکرین‌شات‌ها ═══════════
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
        await update_job_status(job)

    except Exception as e:
        await send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"
        await update_job_status(job)
    finally:
        await page.close()
        shutil.rmtree(job_dir, ignore_errors=True)

# ═══════════ ضبط ویدیو (PulseAudio + ارسال مستقیم) ═══════════
async def process_record_job(job: Job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    url = job.url
    rec_time = session.settings.record_time
    behavior = session.settings.record_behavior
    audio_enabled = session.settings.audio_enabled
    video_format = session.settings.video_format
    delivery = session.settings.video_delivery
    resolution = session.settings.video_resolution
    w, h = ALLOWED_RESOLUTIONS.get(resolution, (1280, 720))
    job_dir = f"jobs/{job.job_id}"
    os.makedirs(job_dir, exist_ok=True)

    behavior_names = {"click": "کلیک هوشمند", "scroll": "اسکرول نرم", "live": "لایو"}
    await send_message(chat_id, f"🎬 ضبط {rec_time} ثانیه ({behavior_names.get(behavior, behavior)})...")

    audio_proc = None
    audio_path = None
    _rec_pw = None
    _rec_browser = None

    try:
        pulse_ok = False
        if audio_enabled:
            pulse_ok = await setup_pulseaudio_async()
            if pulse_ok:
                audio_proc, audio_path = await start_audio_capture_async(job_dir)

        _rec_pw = await async_playwright().start()
        _rec_browser = await _rec_pw.chromium.launch(
            headless=True,
            args=["--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu",
                  "--autoplay-policy=no-user-gesture-required"]
        )
        context = await _rec_browser.new_context(
            viewport={"width": w, "height": h},
            record_video_dir=job_dir,
            record_video_size={"width": w, "height": h}
        )
        page = await context.new_page()

        await page.goto(url, timeout=90000, wait_until="domcontentloaded")
        await page.wait_for_timeout(2000)

        if behavior == "scroll" or (job.extra or {}).get("live_scroll", False):
            await smooth_scroll_to_video(page)
            await page.wait_for_timeout(rec_time * 1000)
        elif behavior == "click":
            vx, vy = await _find_video_center(page)
            await page.mouse.click(vx, vy)
            await page.wait_for_timeout(rec_time * 1000)
        else:  # live
            await page.wait_for_timeout(rec_time * 1000)

        await page.close()
        video_path = await context.close()

        audio_ok = await stop_audio_capture_async(audio_proc, audio_path) if audio_proc else False

        if not video_path or not os.path.exists(video_path):
            await send_message(chat_id, "❌ ویدیویی ضبط نشد.")
            job.status = "error"
            await update_job_status(job)
            return

        final_video_path = video_path
        if video_format != "webm":
            converted = os.path.join(job_dir, f"record.{video_format}")
            cmd = ['ffmpeg', '-y', '-i', video_path, '-c:v', 'libx264', '-c:a', 'copy', converted] if video_format == "mp4" else \
                  ['ffmpeg', '-y', '-i', video_path, '-c', 'copy', converted]
            try:
                proc = await asyncio.create_subprocess_exec(
                    *cmd, stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE
                )
                await proc.communicate()
                if os.path.exists(converted) and os.path.getsize(converted) > 0:
                    final_video_path = converted
                    os.remove(video_path)
            except:
                await safe_log("Video format conversion failed, keeping webm")

        use_zip = (delivery == "zip")

        async def send_file(path, label_prefix, as_zip=False):
            fname = os.path.basename(path)
            if as_zip:
                if os.path.getsize(path) <= ZIP_PART_SIZE:
                    zp = os.path.join(job_dir, f"{fname}.zip")
                    with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as zf:
                        zf.write(path, fname)
                    await send_document(chat_id, zp, caption=f"{label_prefix} (ZIP)")
                    os.remove(zp)
                else:
                    parts = create_zip_and_split(path, fname)
                    for idx, p in enumerate(parts, 1):
                        await send_document(chat_id, p, caption=f"{label_prefix} (ZIP) پارت {idx}/{len(parts)}")
            else:
                base, ext = os.path.splitext(fname)
                if os.path.getsize(path) <= ZIP_PART_SIZE:
                    await send_document(chat_id, path, caption=f"{label_prefix} (اصلی)")
                else:
                    parts = split_file_binary(path, base, ext)
                    for idx, p in enumerate(parts, 1):
                        await send_document(chat_id, p, caption=f"{label_prefix} (اصلی) پارت {idx}/{len(parts)}")

        await send_file(final_video_path, "🎬 ویدیو", use_zip)
        if audio_ok and audio_path and os.path.exists(audio_path):
            await send_file(audio_path, "🎵 صوت", use_zip)

        job.status = "done"
        await update_job_status(job)
        await safe_log(f"Recording done for job {job.job_id}")

    except Exception as e:
        await send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"
        await update_job_status(job)
    finally:
        if _rec_browser:
            try:
                await _rec_browser.close()
            except:
                pass
        if _rec_pw:
            try:
                await _rec_pw.stop()
            except:
                pass
        shutil.rmtree(job_dir, ignore_errors=True)

# ═══════════ دانلود (اصلی، کور، استریم، ADM، وب‌سایت) ═══════════
async def async_crawl_for_download(start_url):
    visited = set()
    q = asyncio.Queue()
    await q.put((start_url, 0))
    s = aiohttp.ClientSession(headers={"User-Agent": "Mozilla/5.0"})
    try:
        while not q.empty():
            cur, depth = await q.get()
            if cur in visited or depth > 1:
                continue
            visited.add(cur)
            try:
                async with s.get(cur, timeout=10) as r:
                    if r.status != 200:
                        continue
                    if is_direct_file_url(cur):
                        return cur
                    ct = r.headers.get("Content-Type", "")
                    if "text/html" in ct:
                        text = await r.text()
                        soup = BeautifulSoup(text, "html.parser")
                        for a in soup.find_all("a", href=True):
                            href = urljoin(cur, a["href"])
                            if is_direct_file_url(href):
                                return href
                            if depth + 1 <= 1:
                                await q.put((href, depth+1))
            except:
                continue
    finally:
        await s.close()
    return None

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
                if resp.headers.get("Content-Length"):
                    size_bytes = int(resp.headers["Content-Length"])
    except:
        pass

    err = await check_rate_limit(chat_id, "download", size_bytes)
    if err:
        await send_message(chat_id, err)
        job.status = "cancelled"
        await update_job_status(job)
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
    await update_job_status(job)

async def process_blind_download(job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    url = job.url
    job_dir = f"jobs/{job.job_id}"
    os.makedirs(job_dir, exist_ok=True)
    await send_message(chat_id, "⏳ دانلود اولیه...")
    try:
        async with aiohttp.ClientSession() as sess:
            async with sess.get(url, headers={"User-Agent": "Mozilla/5.0"}) as r:
                ct = r.headers.get("Content-Type", "application/octet-stream")
                fname = get_filename_from_url(url)
                if '.' not in fname:
                    if "video" in ct:
                        fname += ".mp4"
                    elif "pdf" in ct:
                        fname += ".pdf"
                    else:
                        fname += ".bin"
                fpath = os.path.join(job_dir, fname)
                with open(fpath, "wb") as f:
                    async for chunk in r.content.iter_chunked(8192):
                        f.write(chunk)
        size_bytes = os.path.getsize(fpath)
        size_str = f"{size_bytes/1024/1024:.2f} MB"
        if not session.is_admin:
            err = await check_rate_limit(chat_id, "download", size_bytes)
            if err:
                await send_message(chat_id, err)
                job.status = "cancelled"
                await update_job_status(job)
                return
        kb = {"inline_keyboard": [
            [{"text":"📦 ZIP","callback_data":f"dlblindzip_{job.job_id}"},
             {"text":"📄 اصلی","callback_data":f"dlblindra_{job.job_id}"}],
            [{"text":"❌ لغو","callback_data":f"canceljob_{job.job_id}"}]
        ]}
        await send_message(chat_id, f"📄 فایل (کور): {fname} ({size_str})", reply_markup=kb)
        job.status = "awaiting_user"
        job.extra = {"file_path": fpath, "filename": fname}
        await update_job_status(job)
    except Exception as e:
        await send_message(chat_id, f"❌ دانلود کور ناموفق: {e}")
        job.status = "error"
        await update_job_status(job)
        shutil.rmtree(job_dir, ignore_errors=True)

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
        await update_job_status(job)
        shutil.rmtree(job_dir, ignore_errors=True)
        return

    if mode == "adm":
        await send_message(chat_id, "⚡⚡ دانلود ADM (چندبخشی + قابلیت ادامه)...")
        success = await async_adm_download(extra["direct_link"], extra["filename"], job_dir, chat_id)
        if not success:
            job.status = "error"
            await update_job_status(job)
            shutil.rmtree(job_dir, ignore_errors=True)
            return
    else:
        fpath = os.path.join(job_dir, extra["filename"])
        await send_message(chat_id, "⏳ در حال دانلود...")
        async with aiohttp.ClientSession() as sess:
            async with sess.get(extra["direct_link"]) as resp:
                with open(fpath, "wb") as f:
                    async for chunk in resp.content.iter_chunked(8192):
                        f.write(chunk)

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
    await update_job_status(job)
    shutil.rmtree(job_dir, ignore_errors=True)

async def async_stream_download(url, fname, job_dir, chat_id):
    base, ext = os.path.splitext(fname)
    buf = b""
    idx = 1
    async with aiohttp.ClientSession() as sess:
        async with sess.get(url, headers={"User-Agent": "Mozilla/5.0"}) as r:
            async for chunk in r.content.iter_chunked(8192):
                buf += chunk
                while len(buf) >= ZIP_PART_SIZE:
                    part = buf[:ZIP_PART_SIZE]
                    buf = buf[ZIP_PART_SIZE:]
                    pname = f"{base}.part{idx:03d}{ext}"
                    ppath = os.path.join(job_dir, pname)
                    with open(ppath, "wb") as f:
                        f.write(part)
                    await send_document(chat_id, ppath, caption=f"⚡ پارت {idx}")
                    os.remove(ppath)
                    idx += 1
            if buf:
                pname = f"{base}.part{idx:03d}{ext}"
                ppath = os.path.join(job_dir, pname)
                with open(ppath, "wb") as f:
                    f.write(buf)
                await send_document(chat_id, ppath, caption=f"⚡ پارت {idx}")
                os.remove(ppath)

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

async def download_full_website_async(job):
    chat_id = job.chat_id
    url = job.url
    job_dir = f"jobs/{job.job_id}"
    os.makedirs(job_dir, exist_ok=True)
    await send_message(chat_id, "🌐 دانلود کامل وب‌سایت...")
    if shutil.which("wget"):
        try:
            ua = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"
            cmd = ["wget", "--adjust-extension", "--span-hosts", "--convert-links",
                   "--page-requisites", "--no-directories", "--directory-prefix", job_dir,
                   "--recursive", "--level=1", "--accept", "html,css,js,jpg,jpeg,png,gif,svg,mp4,webm,pdf",
                   "--user-agent", ua, "--header", "Accept: */*", "--timeout", "30", "--tries", "2", url]
            subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)
            await _finish_website_download(job, job_dir)
            return
        except:
            pass
    await send_message(chat_id, "🔄 دانلود با مرورگر مخفی...")
    try:
        context = await get_user_context(chat_id)
        page = await context.new_page()
        await page.goto(url, timeout=60000, wait_until="domcontentloaded")
        await page.wait_for_timeout(3000)
        html = await page.content()
        with open(os.path.join(job_dir, "index.html"), "w", encoding="utf-8") as f:
            f.write(html)
        await page.screenshot(path=os.path.join(job_dir, "screenshot.png"), full_page=True)
        await page.close()
        await _finish_website_download(job, job_dir)
    except Exception as e:
        await send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"
        await update_job_status(job)
        shutil.rmtree(job_dir, ignore_errors=True)

async def _finish_website_download(job, job_dir):
    chat_id = job.chat_id
    all_files = []
    for root, _, files in os.walk(job_dir):
        for f in files:
            all_files.append(os.path.join(root, f))
    if not all_files:
        await send_message(chat_id, "❌ محتوایی یافت نشد.")
        job.status = "error"
        await update_job_status(job)
        return
    zp = os.path.join(job_dir, "website.zip")
    with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as zf:
        for fp in all_files:
            zf.write(fp, os.path.relpath(fp, job_dir))
    parts = split_file_binary(zp, "website", ".zip") if os.path.getsize(zp) > ZIP_PART_SIZE else [zp]
    instr = os.path.join(job_dir, "merge.txt")
    with open(instr, "w") as f:
        f.write("همه‌ی فایل‌ها را دانلود کنید، سپس فایل .001 را با WinRAR یا 7-Zip باز کنید.")
    await send_document(chat_id, instr, caption="📝 راهنما")
    for idx, p in enumerate(parts, 1):
        await send_document(chat_id, p, caption=f"🌐 پارت {idx}/{len(parts)}")
    job.status = "done"
    await update_job_status(job)
    shutil.rmtree(job_dir, ignore_errors=True)

# ═══════════ اسکن و تحلیل ═══════════
async def process_scan_job(job: Job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    if job.mode == "scan_downloads":
        await handle_scan_downloads(job)
    elif job.mode == "scan_videos":
        await handle_scan_videos(job)
    elif job.mode == "extract_commands":
        await handle_extract_commands(job)
    elif job.mode == "smart_analyze":
        await handle_smart_analyze(job)
    elif job.mode == "source_analyze":
        await handle_source_analyze(job)
    elif job.mode == "download_all_found":
        await handle_download_all_found(job)

async def handle_scan_downloads(job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    url = session.browser_url
    if not url:
        await send_message(chat_id, "❌ صفحه‌ای برای جستجو باز نیست.")
        job.status = "done"
        await update_job_status(job)
        return
    deep_mode = session.settings.deep_scan_mode
    await send_message(chat_id, f"🔎 جستجوی فایل‌ها ({deep_mode})...")
    found_links = set()
    all_results = []

    async with aiohttp.ClientSession() as head_sess:
        async def add_result(link):
            if link in found_links:
                return
            found_links.add(link)
            fname = get_filename_from_url(link)
            size_str = "نامشخص"
            size_bytes = None
            try:
                async with head_sess.head(link, timeout=aiohttp.ClientTimeout(total=5),
                                          allow_redirects=True) as resp:
                    if "Content-Length" in resp.headers:
                        size_bytes = int(resp.headers["Content-Length"])
                        size_str = f"{size_bytes/1024/1024:.2f} MB"
            except:
                pass
            if deep_mode == "logical" and not is_direct_file_url(link):
                return
            all_results.append({"name": fname[:35], "url": link, "size": size_str})

        start_time = time.time()
        try:
            context = await get_user_context(chat_id, session.settings.incognito_mode)
            page = await context.new_page()
            await page.goto(url, timeout=30000, wait_until="domcontentloaded")
            await page.wait_for_timeout(1000)
            all_hrefs = await page.evaluate("""() => {
                return Array.from(document.querySelectorAll('a[href]'))
                            .map(a => a.href).filter(h => h.startsWith('http'));
            }""")
            await page.close()
            for href in all_hrefs:
                parsed = urlparse(href)
                if any(ad in parsed.netloc for ad in AD_DOMAINS):
                    continue
                if any(kw in href.lower() for kw in BLOCKED_AD_KEYWORDS):
                    continue
                if is_direct_file_url(href):
                    await add_result(href)
            elapsed = time.time() - start_time
            if all_results:
                await send_message(chat_id, f"✅ مرحله ۱: {len(all_results)} فایل ({elapsed:.1f}s)")
        except Exception as e:
            await safe_log(f"scan_downloads stage1 error: {e}")

        if not all_results and time.time() - start_time < 60:
            await send_message(chat_id, "🔄 مرحله ۲: کراول سبک...")
            try:
                s = aiohttp.ClientSession(headers={"User-Agent": "Mozilla/5.0"})
                async with s.get(url, timeout=10) as resp:
                    if resp.status == 200 and "text/html" in resp.headers.get("Content-Type", ""):
                        text = await resp.text()
                        soup = BeautifulSoup(text, "html.parser")
                        links_to_crawl = []
                        for a in soup.find_all("a", href=True):
                            href = urljoin(url, a["href"])
                            parsed = urlparse(href)
                            if any(ad in parsed.netloc for ad in AD_DOMAINS):
                                continue
                            if any(kw in href.lower() for kw in BLOCKED_AD_KEYWORDS):
                                continue
                            if is_direct_file_url(href):
                                await add_result(href)
                            else:
                                links_to_crawl.append(href)
                        for link in links_to_crawl[:15]:
                            if time.time() - start_time > 60:
                                break
                            found = await async_crawl_for_download(link)
                            if found:
                                await add_result(found)
                        elapsed = time.time() - start_time
                        await send_message(chat_id, f"✅ مرحله ۲: مجموعاً {len(all_results)} فایل ({elapsed:.1f}s)")
                await s.close()
            except Exception as e:
                await safe_log(f"scan_downloads stage2 error: {e}")

    if not all_results:
        await send_message(chat_id, "🚫 هیچ فایل قابل دانلودی یافت نشد.")
        job.status = "done"
        await update_job_status(job)
        return

    session.found_downloads = all_results
    session.found_downloads_page = 0
    await set_session(session)
    await send_found_downloads_page(chat_id, 0)
    job.status = "done"
    await update_job_status(job)

async def send_found_downloads_page(chat_id, page_num=0):
    session = await get_session(chat_id)
    all_results = session.found_downloads or []
    per_page = 10
    start = page_num * per_page
    end = min(start + per_page, len(all_results))
    page_results = all_results[start:end]
    lines = [f"📦 **فایل‌های یافت‌شده (صفحه {page_num+1}/{math.ceil(len(all_results)/per_page)}):**"]
    cmds = {}
    for i, f in enumerate(page_results):
        idx = start + i
        cmd = f"/d{hashlib.md5(f['url'].encode()).hexdigest()[:5]}"
        cmds[cmd] = f['url']
        lines.append(f"{idx+1}. {f['name']} ({f['size']})")
        lines.append(f"   📥 {cmd}    🔗 {f['url'][:60]}")
    nav = []
    if page_num > 0:
        nav.append({"text": "◀️ قبلی", "callback_data": f"dfpg_{chat_id}_{page_num-1}"})
    if end < len(all_results):
        nav.append({"text": "بعدی ▶️", "callback_data": f"dfpg_{chat_id}_{page_num+1}"})
    keyboard_rows = [nav] if nav else []
    keyboard_rows.append([{"text": "📦 دانلود همه (ZIP)", "callback_data": f"dlall_{chat_id}"}])
    keyboard_rows.append([{"text": "❌ بستن", "callback_data": "close_downloads"}])
    await send_message(chat_id, "\n".join(lines), reply_markup={"inline_keyboard": keyboard_rows})
    session.text_links = {**(session.text_links or {}), **cmds}
    await set_session(session)

async def handle_scan_videos(job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    context = await get_user_context(chat_id, session.settings.incognito_mode)
    page = await context.new_page()
    try:
        await page.goto(session.browser_url, timeout=60000, wait_until="domcontentloaded")
        await page.wait_for_timeout(3000)
        videos = await scan_videos_smart(page)
        await page.close()
        if not videos:
            await send_message(chat_id, "🚫 هیچ ویدیویی یافت نشد.")
            job.status = "done"
            await update_job_status(job)
            return
        lines = [f"🎬 **{len(videos)} ویدیو یافت شد:**"]
        cmds = {}
        for i, vid in enumerate(videos[:15]):
            cmd = f"/o{hashlib.md5(vid['href'].encode()).hexdigest()[:5]}"
            cmds[cmd] = vid['href']
            lines.append(f"{i+1}. {vid['text']}")
            lines.append(f"   📥 {cmd}")
        await send_message(chat_id, "\n".join(lines))
        session.text_links = {**(session.text_links or {}), **cmds}
        await set_session(session)
        job.status = "done"
        await update_job_status(job)
    except Exception as e:
        await send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"
        await update_job_status(job)
    finally:
        await page.close()

async def handle_extract_commands(job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    all_links = session.browser_links or []
    if not all_links:
        await send_message(chat_id, "🚫 لینکی برای استخراج وجود ندارد.")
        job.status = "done"
        await update_job_status(job)
        return
    cmds = {}
    lines = [f"📋 **{len(all_links)} فرمان استخراج شد:**"]
    for i, link in enumerate(all_links):
        cmd = f"/H{hashlib.md5(link['href'].encode()).hexdigest()[:5]}"
        cmds[cmd] = link['href']
        line = f"{cmd} : {link['text'][:40]}\n🔗 {link['href'][:80]}"
        lines.append(line)
        if (i+1) % 15 == 0 or i == len(all_links)-1:
            await send_message(chat_id, "\n".join(lines))
            lines = [f"📋 **ادامه فرامین ({i+1}/{len(all_links)}):**"]
    session.text_links = {**(session.text_links or {}), **cmds}
    await set_session(session)
    job.status = "done"
    await update_job_status(job)

async def handle_smart_analyze(job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    all_links = session.browser_links or []
    if not all_links:
        await send_message(chat_id, "🚫 لینکی برای تحلیل وجود ندارد.")
        job.status = "done"
        await update_job_status(job)
        return
    videos = [l for l in all_links if is_direct_file_url(l["href"]) and any(l["href"].lower().endswith(e) for e in ('.mp4','.webm','.mkv','.m3u8','.mpd','.mov','.avi'))]
    files = [l for l in all_links if is_direct_file_url(l["href"]) and l not in videos]
    pages = [l for l in all_links if l not in videos and l not in files]
    cmds = {}
    def send_category(title, items, prefix):
        if not items:
            return
        lines = [f"**{title} ({len(items)}):**"]
        for item in items:
            cmd = f"/{prefix}{hashlib.md5(item['href'].encode()).hexdigest()[:5]}"
            cmds[cmd] = item['href']
            lines.append(f"{cmd} : {item['text'][:40]}\n🔗 {item['href'][:80]}")
        asyncio.create_task(send_message(chat_id, "\n".join(lines)))
    send_category("🎬 ویدیوها", videos, "H")
    send_category("📦 فایل‌ها", files, "H")
    send_category("📄 صفحات", pages[:20], "H")
    if pages[20:]:
        lines = ["🔹 **بقیه صفحات:**"]
        for item in pages[20:]:
            cmd = f"/H{hashlib.md5(item['href'].encode()).hexdigest()[:5]}"
            cmds[cmd] = item['href']
            lines.append(f"{cmd} : {item['text'][:40]}")
        asyncio.create_task(send_message(chat_id, "\n".join(lines)))
    session.text_links = {**(session.text_links or {}), **cmds}
    await set_session(session)
    job.status = "done"
    await update_job_status(job)

async def handle_source_analyze(job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    context = await get_user_context(chat_id, session.settings.incognito_mode)
    page = await context.new_page()
    try:
        await page.goto(session.browser_url, timeout=60000, wait_until="domcontentloaded")
        await page.wait_for_timeout(2000)
        html = await page.content()
        soup = BeautifulSoup(html, "html.parser")
        found_urls = set()
        for tag in soup.find_all(["a","link","script","img","iframe","source","video","audio"]):
            for attr in ("href","src","data-url","data-href","data-link"):
                val = tag.get(attr)
                if val:
                    try:
                        found_urls.add(urljoin(session.browser_url, val))
                    except:
                        pass
        for script in soup.find_all("script"):
            if script.string:
                matches = re.findall(r'https?://[^\s"\'<>]+', script.string)
                for m in matches:
                    found_urls.add(m)
        clean = [u for u in found_urls if not any(ad in u for ad in AD_DOMAINS) and not any(kw in u.lower() for kw in BLOCKED_AD_KEYWORDS)]
        if not clean:
            await send_message(chat_id, "🚫 هیچ لینک مخفی یافت نشد.")
            job.status = "done"
            await update_job_status(job)
            return
        cmds = {}
        lines = [f"🕵️ **{len(clean)} لینک از سورس استخراج شد:**"]
        for i, url in enumerate(clean[:30]):
            cmd = f"/H{hashlib.md5(url.encode()).hexdigest()[:5]}"
            cmds[cmd] = url
            label = urlparse(url).path.split("/")[-1][:30] or url[:40]
            lines.append(f"{cmd} : {label}\n🔗 {url[:80]}")
        await send_message(chat_id, "\n".join(lines))
        session.text_links = {**(session.text_links or {}), **cmds}
        await set_session(session)
        job.status = "done"
        await update_job_status(job)
    except Exception as e:
        await send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"
        await update_job_status(job)
    finally:
        await page.close()

async def handle_download_all_found(job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    all_results = session.found_downloads or []
    if not all_results:
        await send_message(chat_id, "🚫 فایلی برای دانلود وجود ندارد.")
        job.status = "done"
        await update_job_status(job)
        return
    job_dir = f"jobs/{job.job_id}"
    os.makedirs(job_dir, exist_ok=True)
    await send_message(chat_id, f"📦 در حال دانلود {len(all_results)} فایل...")
    downloaded = []
    for f in all_results:
        try:
            fname = get_filename_from_url(f['url'])
            fpath = os.path.join(job_dir, fname)
            async with aiohttp.ClientSession() as sess:
                async with sess.get(f['url'], headers={"User-Agent": "Mozilla/5.0"}) as resp:
                    with open(fpath, "wb") as fh:
                        async for chunk in resp.content.iter_chunked(8192):
                            fh.write(chunk)
            downloaded.append(fpath)
        except Exception as e:
            await safe_log(f"download_all: failed {f['url']}: {e}")
    if not downloaded:
        await send_message(chat_id, "❌ هیچ فایلی دانلود نشد.")
        job.status = "error"
        await update_job_status(job)
        shutil.rmtree(job_dir, ignore_errors=True)
        return
    zp = os.path.join(job_dir, "all_files.zip")
    with zipfile.ZipFile(zp, "w", zipfile.ZIP_DEFLATED) as zf:
        for fp in downloaded:
            zf.write(fp, os.path.basename(fp))
    parts = split_file_binary(zp, "all_files", ".zip") if os.path.getsize(zp) > ZIP_PART_SIZE else [zp]
    instr = os.path.join(job_dir, "merge.txt")
    with open(instr, "w") as f:
        f.write("همه‌ی فایل‌ها را دانلود کنید، سپس فایل .001 را با WinRAR یا 7-Zip باز کنید.")
    await send_document(chat_id, instr, caption="📝 راهنما")
    for idx, p in enumerate(parts, 1):
        await send_document(chat_id, p, caption=f"📦 پارت {idx}/{len(parts)}")
    job.status = "done"
    await update_job_status(job)
    shutil.rmtree(job_dir, ignore_errors=True)

# ═══════════ کپچا، شات کامل، کاوشگر ═══════════
async def process_captcha_job(job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    url = session.browser_url
    if not url:
        await send_message(chat_id, "❌ مرورگری باز نیست.")
        return
    context = await get_user_context(chat_id, session.settings.incognito_mode)
    page = await context.new_page()
    try:
        await page.goto(url, timeout=30000, wait_until="domcontentloaded")
        await page.wait_for_timeout(2000)
        candidates = await page.query_selector_all("button, input[type=submit], a[href*='download'], a[href*='file']")
        for btn in candidates[:5]:
            try:
                await btn.click()
                break
            except:
                pass
        network_urls = []
        def on_resp(response):
            if is_direct_file_url(response.url):
                network_urls.append(response.url)
        page.on("response", on_resp)
        await page.wait_for_timeout(15000)
        try:
            page.remove_listener("response", on_resp)
        except:
            pass
        await page.close()
        if network_urls:
            await send_message(chat_id, "✅ لینک‌های دانلود:\n" + "\n".join(network_urls[:5]))
        else:
            await send_message(chat_id, "🚫 لینک دانلودی یافت نشد.")
    except Exception as e:
        await send_message(chat_id, f"❌ خطا: {e}")
    finally:
        await page.close()
    job.status = "done"
    await update_job_status(job)

async def process_fullpage_screenshot(job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    context = await get_user_context(chat_id, session.settings.incognito_mode)
    page = await context.new_page()
    job_dir = f"jobs/{job.job_id}"
    os.makedirs(job_dir, exist_ok=True)
    try:
        await send_message(chat_id, "📸 در حال بارگذاری کامل صفحه...")
        await page.goto(job.url, timeout=120000, wait_until="domcontentloaded")
        await page.wait_for_timeout(5000)
        spath = os.path.join(job_dir, "fullpage.png")
        await page.screenshot(path=spath, full_page=True)
        await send_document(chat_id, spath, caption="✅ شات کامل")
        job.status = "done"
        await update_job_status(job)
    except Exception as e:
        await send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"
        await update_job_status(job)
    finally:
        await page.close()
        shutil.rmtree(job_dir, ignore_errors=True)

async def process_interactive_scan(job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    url = session.browser_url or job.url
    if not url:
        await send_message(chat_id, "❌ صفحه‌ای برای کاوش باز نیست.")
        job.status = "done"
        await update_job_status(job)
        return
    context = await get_user_context(chat_id, session.settings.incognito_mode)
    page = await context.new_page()
    try:
        await page.goto(url, timeout=60000, wait_until="domcontentloaded")
        await page.wait_for_timeout(2000)
        elements = await page.evaluate("""() => {
            const results = [];
            document.querySelectorAll('input[type="text"], input[type="search"], input[type="email"], input[type="url"], input[type="tel"], input[type="number"], textarea, [contenteditable="true"]').forEach((el, idx) => {
                if (el.offsetWidth === 0 && el.offsetHeight === 0) return;
                const placeholder = el.placeholder || el.getAttribute('aria-label') || el.textContent?.trim()?.substring(0, 50) || 'بدون عنوان';
                const name = el.name || el.id || '';
                let submitBtn = null;
                const form = el.closest('form');
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
                results.push({index: idx+1, type: el.tagName, placeholder, name, selector, submitBtn});
            });
            return results;
        }""")
        await page.close()
        if not elements:
            await send_message(chat_id, "🚫 هیچ فیلد متنی در این صفحه یافت نشد.")
            job.status = "done"
            await update_job_status(job)
            return
        session.interactive_elements = elements
        await set_session(session)
        lines = [f"🔎 **کاوشگر تعاملی ({len(elements)} فیلد)**\n"]
        cmds = {}
        for el in elements:
            cmd = f"/t{el['index']}"
            cmds[cmd] = str(el['index'])
            lines.append(f"{el['index']}. 📝 «{el['placeholder']}» ({el['type']})")
            lines.append(f"   📌 {cmd}\n")
        await send_message(chat_id, "\n".join(lines))
        session.text_links = {**(session.text_links or {}), **cmds}
        await set_session(session)
        job.status = "done"
        await update_job_status(job)
    except Exception as e:
        await send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"
        await update_job_status(job)
    finally:
        await page.close()

async def process_interactive_execute(job):
    chat_id = job.chat_id
    session = await get_session(chat_id)
    extra = job.extra or {}
    element_index = extra.get("element_index", 1)
    user_text = extra.get("user_text", "")
    url = session.browser_url or job.url
    if not url:
        await send_message(chat_id, "❌ صفحه‌ای باز نیست.")
        return
    elements = session.interactive_elements or []
    target = next((el for el in elements if el["index"] == element_index), None)
    if not target:
        await send_message(chat_id, "❌ فیلد مورد نظر یافت نشد.")
        return
    await send_message(chat_id, f"🔎 در حال جستجوی «{user_text}»...")
    context = await get_user_context(chat_id, session.settings.incognito_mode)
    page = await context.new_page()
    job_dir = f"jobs/{job.job_id}"
    os.makedirs(job_dir, exist_ok=True)
    try:
        await page.goto(url, timeout=60000, wait_until="domcontentloaded")
        await page.wait_for_timeout(2000)
        await page.evaluate(f"""([selector, value]) => {{
            const el = document.querySelector(selector) || document.querySelector('input[type="text"], textarea');
            if (el) {{
                el.focus(); el.value = ''; el.value = value;
                el.dispatchEvent(new Event('input', {{ bubbles: true }}));
                el.dispatchEvent(new Event('change', {{ bubbles: true }}));
            }}
        }}""", [target["selector"], user_text])
        await asyncio.sleep(1)
        if target.get("submitBtn"):
            await page.evaluate(f"""([btnText]) => {{
                const btns = document.querySelectorAll('button, input[type="submit"], [role="button"]');
                for (const b of btns) {{
                    if (b.textContent.trim() === btnText) {{ b.click(); return; }}
                }}
            }}""", [target["submitBtn"]["text"]])
        else:
            await page.keyboard.press("Enter")
        await page.wait_for_timeout(10000)
        spath = os.path.join(job_dir, "interactive_result.png")
        await page.screenshot(path=spath, full_page=True)
        await send_document(chat_id, spath, caption=f"📸 نتیجه جستجوی «{user_text}»")
        job.status = "done"
        await update_job_status(job)
    except Exception as e:
        await send_message(chat_id, f"❌ خطا: {e}")
        job.status = "error"
        await update_job_status(job)
    finally:
        await page.close()
        shutil.rmtree(job_dir, ignore_errors=True)

# ═══════════ پنل ادمین ═══════════
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

async def handle_admin_callback(chat_id, data, cid):
    session = await get_session(chat_id)
    if data == "admin_addcode":
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
        session.state = "admin_wait_ban"
        await set_session(session)
        await send_message(chat_id, "⛔ فرمت: `<chat_id> <مدت به دقیقه (اختیاری)>`")
    elif data == "admin_unban":
        session.state = "admin_wait_unban"
        await set_session(session)
        await send_message(chat_id, "✅ فرمت: `<chat_id>`")
    elif data == "admin_users":
        users_list = "\n".join([f"🆔 {uid} – {s.subscription}" for uid, s in sessions.items()])
        await send_message(chat_id, f"👥 کاربران:\n{users_list or 'هیچ کاربری فعال نیست.'}")

# ═══════════ تابع واحد handle_other_callbacks (تمام شاخه‌ها) ═══════════
async def handle_other_callbacks(chat_id, session, data, cid):
    # ── تنظیمات ──
    if data == "set_dlmode":
        modes = ["store","stream","adm"]
        cur = session.settings.default_download_mode
        session.settings.default_download_mode = modes[(modes.index(cur)+1)%3]
        await set_session(session)
        await answer_callback_query(cid, f"✅ دانلود: {session.settings.default_download_mode}")
        await _refresh_settings(chat_id, session)
    elif data == "set_brwmode":
        modes = ["text","media","explorer"]
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
        beh = ["click","scroll","live"]
        cur = session.settings.record_behavior
        session.settings.record_behavior = beh[(beh.index(cur)+1)%3]
        await set_session(session)
        await answer_callback_query(cid, f"✅ رفتار: {session.settings.record_behavior}")
        await _refresh_settings(chat_id, session)
    elif data == "set_audio":
        session.settings.audio_enabled = not session.settings.audio_enabled
        await set_session(session)
        await answer_callback_query(cid, "✅ تغییر یافت")
        await _refresh_settings(chat_id, session)
    elif data == "set_vfmt":
        fmts = ["webm","mkv","mp4"]
        cur = session.settings.video_format
        session.settings.video_format = fmts[(fmts.index(cur)+1)%3]
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
        ress = ["480p","720p","1080p","4k"]
        cur = session.settings.video_resolution
        session.settings.video_resolution = ress[(ress.index(cur)+1)%4]
        await set_session(session)
        await answer_callback_query(cid, f"✅ کیفیت: {session.settings.video_resolution}")
        await _refresh_settings(chat_id, session)
    elif data == "set_rec":
        session.state = "waiting_record_time"
        await set_session(session)
        await send_message(chat_id, "⏱️ زمان ضبط را به ثانیه وارد کنید (۱ تا ۱۸۰۰):")
    elif data == "back_main":
        await send_message(chat_id, "منوی اصلی:", reply_markup=main_menu_keyboard(session.is_admin, session.subscription))

    # ── callbackهای خزنده ──
    elif data == "crawler_mode":
        modes = ["normal","medium","deep"]
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
    elif data in ("crawler_adblock","crawler_sitemap","crawler_priority","crawler_js"):
        attr = {"crawler_adblock":"crawler_adblock","crawler_sitemap":"crawler_sitemap",
                "crawler_priority":"crawler_priority","crawler_js":"crawler_js"}[data]
        setattr(session.settings, attr, not getattr(session.settings, attr))
        await set_session(session)
        await answer_callback_query(cid, "✅ تغییر یافت")
        await _refresh_crawler_settings(chat_id, session)
    elif data == "crawler_start":
        session.state = "waiting_crawler_url"
        await set_session(session)
        await send_message(chat_id, "🔗 لینک شروع خزنده را بفرستید:",
                           reply_markup={"inline_keyboard":[[{"text":"❌ انصراف","callback_data":"crawler_cancel_url"}]]})
    elif data == "crawler_cancel_url":
        session.state = "idle"
        await set_session(session)
        await send_message(chat_id, "❌ خزنده لغو شد.", reply_markup=main_menu_keyboard(session.is_admin, session.subscription))
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
        await send_message(chat_id, "❌ خزنده لغو شد.", reply_markup=main_menu_keyboard(session.is_admin, session.subscription))

    # ── callbackهای مرورگر و لینک‌ها ──
    elif data.startswith("nav_") or data.startswith("dlvid_"):
        async with callback_map_lock:
            url = callback_map.pop(data, None)
        if url:
            await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="browser", url=url))
        else:
            await answer_callback_query(cid, "🔗 لینک نامعتبر یا منقضی شده.")
    elif data.startswith("bpg_"):
        parts = data.split("_")
        if len(parts)==3:
            session.browser_page = int(parts[2])
            await set_session(session)
            await send_browser_page(chat_id, page_num=int(parts[2]))
    elif data.startswith("closebrowser_"):
        session.browser_links = None
        session.browser_url = None
        session.state = "idle"
        await set_session(session)
        await send_message(chat_id, "🧭 بسته شد.", reply_markup=main_menu_keyboard(session.is_admin, session.subscription))

    # ── callbackهای اسکرین‌شات 2x/4k ──
    elif data.startswith("req2x_"):
        jid = data[6:]
        job = await find_job(jid)
        if job and job.status == "done":
            await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="2x_screenshot", url=job.url))
    elif data.startswith("req4k_"):
        jid = data[6:]
        job = await find_job(jid)
        if job and job.status == "done":
            await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="4k_screenshot", url=job.url))

    # ── callbackهای دانلود ──
    elif data.startswith("dlzip_") or data.startswith("dlraw_"):
        jid = data[6:] if data.startswith("dlzip_") else data[6:]
        job = await find_job(jid)
        if job and job.extra:
            job.extra["pack_zip"] = data.startswith("dlzip_")
            job.status = "done"
            await update_job_status(job)
            await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="download_execute", url=job.url, extra=job.extra))
    elif data.startswith("dlblindzip_") or data.startswith("dlblindra_"):
        jid = data[11:] if data.startswith("dlblindzip_") else data[11:]
        job = await find_job(jid)
        if job and job.extra and "file_path" in job.extra:
            job.extra["pack_zip"] = data.startswith("dlblindzip_")
            job.status = "done"
            await update_job_status(job)
            await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="download_execute", url=job.url, extra=job.extra))
    elif data.startswith("canceljob_"):
        jid = data[10:]
        job = await find_job(jid)
        if job:
            job.status = "cancelled"
            await update_job_status(job)
        await send_message(chat_id, "❌ لغو شد.", reply_markup=main_menu_keyboard(session.is_admin, session.subscription))

    # ── callbackهای اسکن، تحلیل، ضبط، کپچا و ... ──
    elif data.startswith("scvid_"):
        await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="scan_videos", url=""))
    elif data.startswith("scdl_"):
        await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="scan_downloads", url=""))
    elif data.startswith("extcmd_"):
        await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="extract_commands", url=""))
    elif data.startswith("sman_"):
        await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="smart_analyze", url=""))
    elif data.startswith("srcan_"):
        await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="source_analyze", url=""))
    elif data.startswith("recvid_"):
        if session.settings.record_behavior == "live":
            session.state = "waiting_live_command"
            await set_session(session)
            await send_message(chat_id, "🎭 حالت Live فعال است. لطفاً دستور Live را وارد کنید:")
        elif session.browser_url:
            await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="record_video", url=session.browser_url, queue_type="record"))
        else:
            await answer_callback_query(cid, "❌ مرورگری باز نیست.")
    elif data.startswith("fullshot_"):
        if session.browser_url:
            await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="fullpage_screenshot", url=session.browser_url))
        else:
            await answer_callback_query(cid, "❌ مرورگری باز نیست.")
    elif data.startswith("dlweb_"):
        if session.browser_url:
            await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="download_website", url=session.browser_url))
        else:
            await answer_callback_query(cid, "❌ مرورگری باز نیست.")
    elif data.startswith("intscan_"):
        if session.browser_url:
            await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="interactive_scan", url=session.browser_url))
        else:
            await answer_callback_query(cid, "❌ مرورگری باز نیست.")
    elif data.startswith("captcha_"):
        if session.browser_url:
            await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="captcha", url=""))
        else:
            await answer_callback_query(cid, "❌ مرورگری باز نیست.")

    # ── callbackهای جستجوی فایل‌ها ──
    elif data.startswith("dfpg_"):
        parts = data.split("_")
        if len(parts) == 3:
            page = int(parts[2])
            session.found_downloads_page = page
            await set_session(session)
            await send_found_downloads_page(chat_id, page)
    elif data == "close_downloads":
        session.found_downloads = None
        session.found_downloads_page = 0
        await set_session(session)
        await send_message(chat_id, "📦 نتایج جستجو بسته شد.", reply_markup=main_menu_keyboard(session.is_admin, session.subscription))
    elif data.startswith("dlall_"):
        await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="download_all_found", url=""))

    # ── مسدودسازی تبلیغات ──
    elif data.startswith("adblock_"):
        parsed_url = urlparse(session.browser_url or "")
        current_domain = parsed_url.netloc.lower()
        if not current_domain:
            await answer_callback_query(cid, "دامنه‌ای برای مسدودسازی شناسایی نشد.")
            return
        if session.ad_blocked_domains is None:
            session.ad_blocked_domains = []
        if current_domain in session.ad_blocked_domains:
            session.ad_blocked_domains.remove(current_domain)
            await answer_callback_query(cid, "🛡️ مسدودساز غیرفعال شد.")
        else:
            session.ad_blocked_domains.append(current_domain)
            await answer_callback_query(cid, "🛡️ مسدودساز فعال شد.")
        await set_session(session)
        await send_browser_page(chat_id, page_num=session.browser_page)

    # ── ادمین ──
    elif data.startswith("admin_"):
        await handle_admin_callback(chat_id, data, cid)

    else:
        await answer_callback_query(cid, "⚠️ این دکمه تعریف نشده است.")

# ═══════════ handle_callback اصلی ═══════════
async def handle_callback(cq: dict):
    cid = cq["id"]
    msg = cq.get("message")
    data = cq.get("data", "")
    if not msg:
        return await answer_callback_query(cid)
    chat_id = msg["chat"]["id"]
    session = await get_session(chat_id)

    if not session.is_admin:
        if session.click_counter >= 5:
            await answer_callback_query(cid, "⛔ به حداکثر کلیک (۵) رسیدید. /cancel را بزنید.", show_alert=True)
            return
        session.click_counter += 1
        await set_session(session)

    try:
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
            msg_res = await send_message(chat_id, "⚙️ تنظیمات:", reply_markup=kb)
            if msg_res and "message_id" in msg_res:
                session.last_settings_msg_id = str(msg_res["message_id"])
                await set_session(session)
        elif data == "menu_admin":
            if session.is_admin:
                await admin_panel(chat_id)
            else:
                await answer_callback_query(cid, "⛔ دسترسی غیرمجاز")
        elif data == "menu_help":
            await send_message(chat_id, "راهنما: برای استفاده از هر بخش روی دکمه مورد نظر کلیک کنید و لینک را ارسال نمایید.")
        elif data == "menu_crawler":
            kb = crawler_settings_keyboard(session.settings)
            msg_res = await send_message(chat_id, "🕸️ تنظیمات خزنده وحشی:", reply_markup=kb)
            if msg_res and "message_id" in msg_res:
                session.last_crawler_msg_id = str(msg_res["message_id"])
                await set_session(session)
        else:
            await handle_other_callbacks(chat_id, session, data, cid)
    except Exception as e:
        await safe_log(f"Callback error: {e}")
        await answer_callback_query(cid, "خطایی رخ داد.")

# ═══════════ مدیریت پیام‌ها و Live ═══════════
async def handle_message(chat_id: int, text: str):
    session = await get_session(chat_id)
    try:
        if await is_banned(chat_id):
            await send_message(chat_id, "🚫 شما تحریم هستید.")
            return
        if service_disabled and not session.is_admin:
            await send_message(chat_id, "⛔ سرویس موقتاً غیرفعال است.")
            return

        if not session.is_admin and session.subscription == "free":
            level = await activate_code(chat_id, text)
            if level:
                session.subscription = level
                await set_session(session)
                await send_message(chat_id, f"✅ اشتراک {level} فعال شد!",
                                   reply_markup=main_menu_keyboard(session.is_admin, session.subscription))
            else:
                await send_message(chat_id, "⛔ کد نامعتبر است یا قبلاً استفاده شده.")
            return

        if session.is_admin:
            if session.state == "admin_wait_code":
                parts = text.split()
                if len(parts) == 2 and parts[0] in ("bronze", "plus", "pro"):
                    level, code = parts
                    if await add_code(level, code):
                        await send_message(chat_id, f"✅ کد {code} به سطح {level} اضافه شد.")
                    else:
                        await send_message(chat_id, "⛔ کد تکراری یا سطح نامعتبر.")
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
            if mode:
                qtype = "record" if mode == "record_video" else "general"
                job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode=mode, url=url, queue_type=qtype)
                await enqueue_job(job)
                session.state = "idle"
                await set_session(session)
                await send_message(chat_id, "✅ در صف قرار گرفت.")
            return

        if session.state == "waiting_record_time":
            try:
                val = int(text)
                if 1 <= val <= 1800:
                    session.settings.record_time = val
                    session.state = "idle"
                    await set_session(session)
                    await send_message(chat_id, f"⏱️ زمان ضبط روی {val} ثانیه تنظیم شد.")
                    if session.last_settings_msg_id:
                        await edit_message_reply_markup(chat_id, session.last_settings_msg_id,
                                                        settings_keyboard(session.settings, session.subscription))
                else:
                    await send_message(chat_id, "❌ عدد باید بین ۱ تا ۱۸۰۰ باشد.")
            except:
                await send_message(chat_id, "❌ لطفاً یک عدد وارد کنید.")
            return

        if session.state == "waiting_live_command":
            if text.startswith("/Live_"):
                parts = text[6:]
                need_scroll = parts.endswith("_S")
                if need_scroll:
                    parts = parts[:-2]
                url = parts if parts.startswith("http") else session.text_links.get(parts)
                if url:
                    await handle_live_command(chat_id, url, need_scroll)
                else:
                    await send_message(chat_id, "❌ دستور Live نامعتبر.")
            else:
                await send_message(chat_id, "❌ لطفاً یک دستور Live معتبر ارسال کنید.")
            return

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

        if text == "/start":
            session.state = "idle"
            await set_session(session)
            await send_message(chat_id, "منوی اصلی:", reply_markup=main_menu_keyboard(session.is_admin, session.subscription))
        elif text == "/cancel":
            session.cancel_requested = True
            await set_session(session)
            await send_message(chat_id, "⏹️ درخواست لغو ثبت شد.")
        elif session.state == "browsing" and text in session.text_links:
            url = session.text_links.pop(text)
            await set_session(session)
            await enqueue_job(Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="browser", url=url))
        else:
            await send_message(chat_id, "از منو استفاده کنید:", reply_markup=main_menu_keyboard(session.is_admin, session.subscription))

    except Exception as e:
        await safe_log(f"Message handling error: {e}")

async def handle_live_command(chat_id, url, need_scroll=False):
    session = await get_session(chat_id)
    rec_time = session.settings.record_time
    if url.startswith(("http://", "https://")):
        job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="record_video", url=url)
        job.extra = {"live_scroll": need_scroll}
        await enqueue_job(job)
        await send_message(chat_id, f"🎬 ضبط Live آغاز شد ({rec_time} ثانیه)...")
    else:
        if not session.browser_url:
            await send_message(chat_id, "❌ مرورگری برای اجرای Live باز نیست.")
            return
        context = await get_user_context(chat_id, session.settings.incognito_mode)
        page = await context.new_page()
        try:
            await page.goto(session.browser_url, timeout=60000, wait_until="domcontentloaded")
            await page.wait_for_timeout(2000)
            await page.evaluate(f"""() => {{
                const links = document.querySelectorAll('a[href]');
                for (const a of links) {{
                    if (a.href === '{url}') {{ a.click(); return; }}
                }}
            }}""")
            await page.wait_for_timeout(3000)
            if need_scroll:
                await smooth_scroll_to_video(page)
            job = Job(job_id=str(uuid.uuid4()), chat_id=chat_id, mode="record_video", url=page.url)
            await enqueue_job(job)
            await send_message(chat_id, f"🎬 ضبط Live آغاز شد ({rec_time} ثانیه)...")
        except Exception as e:
            await send_message(chat_id, f"❌ خطا: {e}")
        finally:
            await page.close()

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
            await safe_log(f"Poll error: {e}")
            await asyncio.sleep(5)

async def main():
    await load_subscriptions()
    await init_browsers()
    for _ in range(3):
        asyncio.create_task(general_worker())
    asyncio.create_task(record_worker())
    asyncio.create_task(cleanup_expired_contexts())
    asyncio.create_task(polling_loop())
    await safe_log("✅ Bot-Final اجرا شد")
    await asyncio.Future()

if __name__ == "__main__":
    asyncio.run(main())
