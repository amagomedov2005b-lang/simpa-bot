import asyncio
import json
import logging
import math
import os
import re
import tempfile
import time
from collections import defaultdict, deque
from datetime import datetime
from html import escape
from typing import Optional

import aiosqlite
from aiogram import Bot, Dispatcher, F, BaseMiddleware
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import CommandStart, Command
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    Message, CallbackQuery, LabeledPrice, PreCheckoutQuery, BotCommand,
    InlineKeyboardMarkup, InlineKeyboardButton,
    ReplyKeyboardMarkup, KeyboardButton, ReplyKeyboardRemove,
    InputMediaPhoto,
)

# ==================== CONFIG ====================
BOT_TOKEN = "8925786167:AAFtKY7mDGVM8GT1wRMM2pdvdvejpWPGpx8"   # @simpa_dating_bot
ADMIN_IDS = {1212267117}                 # твой Telegram ID (админ)
MOD_CHAT_ID = 0                          # ID чата уведомлений; 0 = первому админу в ЛС
DB = "dating.db"

MAX_PHOTOS = 3
REPORTS_TO_HIDE = 3                       # жалоб от РАЗНЫХ людей -> анкета скрывается на проверку
DAILY_REPORTS = 6                         # сколько жалоб можно подать в сутки (скользящие 24ч)
SWIPE_MIN_INTERVAL = 0.4                  # сек между свайпами (антифлуд)
SWIPE_DAILY_LIMIT = 500                   # макс свайпов в сутки
BATCH = 400                               # пул кандидатов для сортировки по расстоянию
MAX_STRIKES = 3                           # нарушений до бана
MSG_LIMIT = 200                           # лимит символов сообщения при лайке

# --- Монетизация (звёзды, валюта XTR) ---
SUPER_PRICE = 50                          # 💎 Супер Премиум
MEDIUM_PRICE = 25                         # ⭐ Премиум
TOP_DURATION = 86400                      # топ строго на 24 часа
BOOST_PRICE, BOOST_SECONDS = 10, 30 * 60
LIKES_PRICE, LIKES_SECONDS = 50, 7 * 86400
UNBAN_PRICE = 50                          # самостоятельный разбан

# --- Рефералы ---
REF_NEEDED = 3                            # приглашённых за 1 день топа
REF_REWARD_DAYS = 1                       # дней ⭐ Премиума за каждые REF_NEEDED

# --- Цензура фото (18+) ---
EXPLICIT_NUDE_CLASSES = {
    "FEMALE_GENITALIA_EXPOSED", "MALE_GENITALIA_EXPOSED",
    "FEMALE_BREAST_EXPOSED", "ANUS_EXPOSED", "BUTTOCKS_EXPOSED",
}
NUDE_MIN_SCORE = 0.45
NSFW_SAFE, NSFW_UNSAFE = 0.30, 0.85       # пороги запасной модели opennsfw2

# --- Цензура текста (в описании, на фото через OCR, и в сообщениях) ---
BANNED_WORDS = {
    "сука", "блять", "блядь", "хуй", "пизд", "ебан", "ебал", "мудак", "гондон",
    "долбоёб", "уебок", "fuck", "shit", "bitch", "nigger", "faggot",
}
SEXUAL_WORDS = {
    "секс", "порно", "porn", "интим", "шлюх", "проститут", "эскорт",
    "минет", "анал", "оргия", "вирт", "дрочи", "сперма", "оральн",
    "разврат", "sext", "nudes", "ню фото", "интимн", "куни", "сосу",
}
URL_RE = re.compile(r'(https?://|www\.)\S+', re.I)
DOMAIN_RE = re.compile(
    r'\b[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?\.'
    r'(?:com|ru|net|org|io|me|info|biz|online|site|xyz|app|dev|co|tv|cc|gg|to|su|ua|by|kz|club|shop|store|link|page|pro)'
    r'\b(?:/\S*)?', re.I)
# ================================================

logging.basicConfig(level=logging.INFO)
bot = Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
dp = Dispatcher(storage=MemoryStorage())
db: aiosqlite.Connection = None  # type: ignore
BOT_USERNAME = ""  # заполнится при старте

# ---- Цензура фото: ленивая загрузка ----
NUDE_DETECTOR = None
NUDE_OK = False
OPENNSFW_OK = False
OCR_OK = False
try:
    from nudenet import NudeDetector  # noqa
    NUDE_OK = True
except Exception:
    try:
        import opennsfw2 as _n2  # noqa
        OPENNSFW_OK = True
    except Exception:
        logging.warning("Нет ни NudeNet, ни opennsfw2 -> фото на ручную модерацию")
try:
    import pytesseract  # noqa
    from PIL import Image  # noqa
    OCR_OK = True
except Exception:
    logging.warning("pytesseract/Pillow не установлены -> текст на фото не проверяется")

# ---- runtime state ----
QUEUE: dict[int, deque] = defaultdict(deque)
CURRENT: dict[int, dict] = {}
SWIPE_TS: dict[int, float] = {}
SWIPE_DAY: dict[int, list] = defaultdict(lambda: [0, 0.0])
NEARBY_NOTIFIED: set[int] = set()
PENDING_MSG: dict[int, int] = {}          # uid -> target uid (ждём текст сообщения для лайка)
APPEAL_WAIT: set[int] = set()             # uid пишет текст апелляции
PENDING_REF: dict[int, int] = {}          # новый uid -> кто пригласил (до создания анкеты)
BROADCAST_PENDING: dict[int, str] = {}    # админ uid -> текст рассылки (ждёт подтверждения)
# история для кнопки "Назад": uid -> {"items": [список row-анкет, до 3], "ts": время последнего действия}
SWIPE_HISTORY: dict[int, dict] = {}
HISTORY_MAX = 3                           # сколько предыдущих анкет помнить
HISTORY_TTL = 1800                        # 30 минут жизни истории в RAM

LINE = "━━━━━━━━━━━━━"


# ==================== DB ====================
async def init_db():
    global db
    db = await aiosqlite.connect(DB)
    db.row_factory = aiosqlite.Row
    await db.execute("PRAGMA journal_mode=WAL")
    await db.execute("PRAGMA synchronous=NORMAL")
    await db.execute("PRAGMA temp_store=MEMORY")
    await db.executescript("""
    CREATE TABLE IF NOT EXISTS users(
        uid INTEGER PRIMARY KEY,
        name TEXT, age INTEGER, gender TEXT, looking TEXT,
        about TEXT, photos TEXT,
        lat REAL, lon REAL,
        status TEXT DEFAULT 'pending',
        reject_reason TEXT DEFAULT '',
        strikes INTEGER DEFAULT 0,
        top_tier INTEGER DEFAULT 0,
        top_until INTEGER DEFAULT 0,
        boost_until INTEGER DEFAULT 0,
        likes_until INTEGER DEFAULT 0,
        f_age_min INTEGER DEFAULT 14,
        f_age_max INTEGER DEFAULT 99,
        f_dist INTEGER DEFAULT 0,
        referrer INTEGER DEFAULT 0,
        ref_count INTEGER DEFAULT 0,
        ref_progress INTEGER DEFAULT 0,
        report_count INTEGER DEFAULT 0,
        report_window INTEGER DEFAULT 0,
        created INTEGER
    );
    CREATE TABLE IF NOT EXISTS likes(
        who INTEGER, whom INTEGER, ts INTEGER, PRIMARY KEY(who, whom)
    );
    CREATE TABLE IF NOT EXISTS seen(
        who INTEGER, whom INTEGER, PRIMARY KEY(who, whom)
    );
    CREATE TABLE IF NOT EXISTS reports(
        who INTEGER, whom INTEGER, ts INTEGER, PRIMARY KEY(who, whom)
    );
    CREATE TABLE IF NOT EXISTS payments(
        charge_id TEXT PRIMARY KEY, uid INTEGER, amount INTEGER, kind TEXT, ts INTEGER
    );
    CREATE TABLE IF NOT EXISTS admins(
        uid INTEGER PRIMARY KEY, added_by INTEGER, ts INTEGER
    );
    CREATE TABLE IF NOT EXISTS appeals(
        uid INTEGER PRIMARY KEY, text TEXT, ts INTEGER
    );
    CREATE INDEX IF NOT EXISTS idx_users_status ON users(status);
    CREATE INDEX IF NOT EXISTS idx_likes_whom ON likes(whom);
    CREATE INDEX IF NOT EXISTS idx_seen_who ON seen(who);
    CREATE INDEX IF NOT EXISTS idx_reports_whom ON reports(whom);
    """)
    await db.commit()
    await migrate()


async def migrate():
    """Безопасно дописывает недостающие колонки. Новое поле -> добавь сюда."""
    cur = await db.execute("PRAGMA table_info(users)")
    cols = {r["name"] for r in await cur.fetchall()}
    migrations = {
        "strikes": "INTEGER DEFAULT 0",
        "top_tier": "INTEGER DEFAULT 0",
        "referrer": "INTEGER DEFAULT 0",
        "ref_count": "INTEGER DEFAULT 0",
        "ref_progress": "INTEGER DEFAULT 0",
        "report_count": "INTEGER DEFAULT 0",
        "report_window": "INTEGER DEFAULT 0",
    }
    changed = False
    for col, decl in migrations.items():
        if col not in cols:
            await db.execute(f"ALTER TABLE users ADD COLUMN {col} {decl}")
            changed = True
            logging.info(f"migrate: добавлена колонка {col}")
    if changed:
        await db.commit()


async def get_user(uid: int) -> Optional[aiosqlite.Row]:
    cur = await db.execute("SELECT * FROM users WHERE uid=?", (uid,))
    return await cur.fetchone()


def invalidate(uid: int):
    QUEUE.pop(uid, None)


# ==================== HELPERS ====================
ADMIN_CACHE: set[int] = set()   # динамические админы из БД (подгружаются при старте)

async def load_admins():
    global ADMIN_CACHE
    cur = await db.execute("SELECT uid FROM admins")
    ADMIN_CACHE = {r["uid"] for r in await cur.fetchall()}

def all_admins() -> set:
    return set(ADMIN_IDS) | ADMIN_CACHE

def is_admin(uid: int) -> bool:
    return uid in ADMIN_IDS or uid in ADMIN_CACHE

async def broadcast_admins(text: str, photo: str = None, kb=None):
    """Шлёт уведомление ВСЕМ админам в личку."""
    for aid in all_admins():
        try:
            if photo:
                await bot.send_photo(aid, photo, caption=text, reply_markup=kb)
            else:
                await bot.send_message(aid, text, reply_markup=kb)
        except Exception:
            pass


def esc(s) -> str:
    return escape(str(s))


def fmt_dt(ts: int) -> str:
    return datetime.fromtimestamp(ts).strftime("%d.%m в %H:%M")


def haversine(lat1, lon1, lat2, lon2) -> float:
    R = 6371.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dl = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))


def photos_of(row) -> list:
    try:
        return json.loads(row["photos"]) or []
    except Exception:
        return []


def now() -> int:
    return int(time.time())


def top_active(row) -> bool:
    return bool(row["top_until"]) and row["top_until"] > now()


def badges(row) -> str:
    b = ""
    if top_active(row):
        if row["top_tier"] == 3:
            b += "👑"
        elif row["top_tier"] == 2:
            b += "💎"
        else:
            b += "⭐"
    if row["boost_until"] and row["boost_until"] > now():
        b += "🚀"
    return (b + " ") if b else ""


def distance_label(viewer, row) -> str:
    if viewer is not None and viewer["lat"] is not None and row["lat"] is not None:
        d = haversine(viewer["lat"], viewer["lon"], row["lat"], row["lon"])
        if d < 1:
            return "📍 меньше 1 км от тебя"
        return f"📍 ~{d:.0f} км от тебя"
    return "📍 рядом"


def profile_caption(row, viewer=None) -> str:
    head = f"{badges(row)}<b>{esc(row['name'])}</b>, {row['age']}"
    loc = distance_label(viewer, row)
    return f"{head}\n{loc}\n\n<blockquote>{esc(row['about'])}</blockquote>"


def own_profile_caption(row) -> str:
    status_map = {
        "active": "✅ опубликована", "pending": "🕓 на модерации",
        "paused": "⏸ скрыта вручную", "rejected": "❌ отклонена",
        "hidden": "🚫 на проверке (жалобы)", "banned": "⛔ заблокирована",
    }
    s = status_map.get(row["status"], row["status"])
    extra = ""
    if row["status"] == "rejected" and row["reject_reason"]:
        extra = f"\n<i>Причина: {esc(row['reject_reason'])}</i>"
    promo = ""
    if top_active(row):
        if row["top_tier"] == 3:
            tier_name = "👑 VIP"
        elif row["top_tier"] == 2:
            tier_name = "💎 Супер Премиум"
        else:
            tier_name = "⭐ Премиум"
        promo = f"\n{tier_name} до {fmt_dt(row['top_until'])}"
    strikes = ""
    if row["strikes"]:
        strikes = f"\n⚠️ Нарушений: {row['strikes']}/{MAX_STRIKES}"
    return profile_caption(row) + f"\n\n<b>Статус:</b> {s}{extra}{promo}{strikes}"


def unban_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"💳 Снять блокировку · {UNBAN_PRICE} ⭐", callback_data="unban_pay")],
        [InlineKeyboardButton(text="🛟 Это ошибка — на пересмотр", callback_data="appeal_start")],
    ])

def appeal_only_kb():
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="🛟 Это ошибка — на пересмотр", callback_data="appeal_start")
    ]])


# ==================== KEYBOARDS ====================
def main_menu():
    return ReplyKeyboardMarkup(
        keyboard=[
            [KeyboardButton(text="🔍 Смотреть анкеты")],
            [KeyboardButton(text="👤 Моя анкета"), KeyboardButton(text="💞 Мои метчи")],
            [KeyboardButton(text="❤️ Кто меня лайкнул"), KeyboardButton(text="🚀 Поднять анкету")],
            [KeyboardButton(text="🎁 Пригласить друзей")],
            [KeyboardButton(text="⚙️ Фильтры"), KeyboardButton(text="✏️ Изменить")],
            [KeyboardButton(text="⏸ Скрыть/Показать"), KeyboardButton(text="🗑 Удалить")],
        ],
        resize_keyboard=True,
    )

def gender_kb():
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="👨 Парень", callback_data="g_m"),
        InlineKeyboardButton(text="👩 Девушка", callback_data="g_f"),
    ]])

def looking_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="👨 Парней", callback_data="l_m"),
         InlineKeyboardButton(text="👩 Девушек", callback_data="l_f")],
        [InlineKeyboardButton(text="🌈 Всех", callback_data="l_a")],
    ])

def photos_done_kb(n):
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text=f"✅ Готово ({n}/{MAX_PHOTOS})", callback_data="ph_done")
    ]])

def loc_kb():
    return ReplyKeyboardMarkup(
        keyboard=[[KeyboardButton(text="📍 Отправить геолокацию", request_location=True)]],
        resize_keyboard=True, one_time_keyboard=True,
    )

def swipe_kb(target, photos_count, has_back=False):
    rows = []
    if photos_count > 1:
        rows.append([
            InlineKeyboardButton(text="◀️", callback_data="pprev"),
            InlineKeyboardButton(text=f"1/{photos_count}", callback_data="noop"),
            InlineKeyboardButton(text="▶️", callback_data="pnext"),
        ])
    rows.append([
        InlineKeyboardButton(text="❤️ Лайк", callback_data=f"like_{target}"),
        InlineKeyboardButton(text="💌 Лайк + сообщение", callback_data=f"likemsg_{target}"),
    ])
    bottom = [
        InlineKeyboardButton(text="👎", callback_data=f"dislike_{target}"),
        InlineKeyboardButton(text="🚩 Жалоба", callback_data=f"report_{target}"),
        InlineKeyboardButton(text="💤 Хватит", callback_data="stop"),
    ]
    rows.append(bottom)
    if has_back:
        rows.append([InlineKeyboardButton(text="⬅️ Предыдущая анкета", callback_data="goback")])
    return InlineKeyboardMarkup(inline_keyboard=rows)

def promo_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"💎 Супер Премиум · {SUPER_PRICE} ⭐", callback_data="buy_super")],
        [InlineKeyboardButton(text=f"⭐ Премиум · {MEDIUM_PRICE} ⭐", callback_data="buy_medium")],
        [InlineKeyboardButton(text=f"🚀 Буст 30 мин · {BOOST_PRICE} ⭐", callback_data="buy_boost")],
    ])

def filters_kb(u):
    dist = "не важно" if not u["f_dist"] else f"{u['f_dist']} км"
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text=f"🎂 Возраст: {u['f_age_min']}–{u['f_age_max']}", callback_data="f_age")],
        [InlineKeyboardButton(text=f"📍 Радиус: {dist}", callback_data="f_dist")],
        [InlineKeyboardButton(text="♻️ Сбросить фильтры", callback_data="f_reset")],
    ])

def dist_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="10 км", callback_data="dist_10"),
         InlineKeyboardButton(text="30 км", callback_data="dist_30"),
         InlineKeyboardButton(text="100 км", callback_data="dist_100")],
        [InlineKeyboardButton(text="Не важно", callback_data="dist_0")],
    ])

def review_kb(uid):
    """Скрытая админская проверка по жалобам."""
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Вернуть (жалобы напрасны)", callback_data=f"rev_ok_{uid}"),
        InlineKeyboardButton(text="❌ Отклонить", callback_data=f"rev_no_{uid}"),
    ]])

def appeal_kb(uid):
    """Решение админа по апелляции (пересмотр блокировки)."""
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Разблокировать", callback_data=f"apl_ok_{uid}"),
        InlineKeyboardButton(text="❌ Отклонить апелляцию", callback_data=f"apl_no_{uid}"),
    ]])


# ==================== MIDDLEWARE (бан-гард) ====================
class BanGuard(BaseMiddleware):
    async def __call__(self, handler, event, data):
        uid = getattr(getattr(event, "from_user", None), "id", None)
        if uid is None:
            return await handler(event, data)
        cur = await db.execute("SELECT status FROM users WHERE uid=?", (uid,))
        r = await cur.fetchone()
        if not r or r["status"] != "banned":
            return await handler(event, data)
        # забанен: пропускаем оплату разбана и апелляцию
        if isinstance(event, Message) and event.successful_payment:
            return await handler(event, data)
        if isinstance(event, CallbackQuery) and event.data in ("unban_pay", "appeal_start"):
            return await handler(event, data)
        # пропускаем текст апелляции, если пользователь сейчас её пишет
        if isinstance(event, Message) and uid in APPEAL_WAIT:
            return await handler(event, data)
        ban_text = (f"⛔ <b>Вы заблокированы</b>\n{LINE}\n"
                    f"Превышен лимит нарушений ({MAX_STRIKES}).\n"
                    f"Снять блокировку можно за {UNBAN_PRICE} ⭐.")
        if isinstance(event, Message):
            await event.answer(ban_text, reply_markup=unban_kb())
        elif isinstance(event, CallbackQuery):
            await event.answer("Вы заблокированы.", show_alert=True)
        return

dp.message.middleware(BanGuard())
dp.callback_query.middleware(BanGuard())


# ==================== FSM ====================
class Reg(StatesGroup):
    name = State(); age = State(); gender = State(); looking = State()
    about = State(); photos = State(); location = State()

class Filt(StatesGroup):
    age = State()


# ==================== ЦЕНЗУРА ====================
async def _download_temp(file_id: str) -> str:
    f = await bot.get_file(file_id)
    fd, path = tempfile.mkstemp(suffix=".jpg")
    os.close(fd)
    await bot.download_file(f.file_path, destination=path)
    return path

def _photo_nsfw_sync(path: str) -> str:
    if NUDE_OK:
        try:
            dets = NUDE_DETECTOR.detect(path)
            for d in dets:
                if d.get("class") in EXPLICIT_NUDE_CLASSES and d.get("score", 0) >= NUDE_MIN_SCORE:
                    return "unsafe"
            return "safe"
        except Exception as e:
            logging.warning(f"nudenet fail: {e}")
            return "unknown"
    if OPENNSFW_OK:
        try:
            p = float(_n2.predict_image(path))
            if p > NSFW_UNSAFE:
                return "unsafe"
            if p < NSFW_SAFE:
                return "safe"
            return "review"
        except Exception as e:
            logging.warning(f"opennsfw fail: {e}")
            return "unknown"
    return "unknown"

def _ocr_sync(path: str) -> str:
    if not OCR_OK:
        return ""
    try:
        return pytesseract.image_to_string(Image.open(path), lang="rus+eng")
    except Exception as e:
        logging.warning(f"ocr fail: {e}")
        return ""

def _escalate(a: str, b: str) -> str:
    order = {"unsafe": 0, "review": 1, "unknown": 2, "safe": 3}
    return a if order[a] <= order[b] else b

async def analyze_photos(file_ids: list) -> tuple:
    """(nsfw_verdict, ocr_text). nsfw: unsafe|safe|review|unknown"""
    if not (NUDE_OK or OPENNSFW_OK or OCR_OK):
        return "unknown", ""
    seen_model = NUDE_OK or OPENNSFW_OK
    worst = "safe" if seen_model else "unknown"
    ocr_parts = []
    for fid in file_ids[:MAX_PHOTOS]:
        path = None
        try:
            path = await _download_temp(fid)
            if seen_model:
                worst = _escalate(worst, await asyncio.to_thread(_photo_nsfw_sync, path))
            if OCR_OK:
                ocr_parts.append(await asyncio.to_thread(_ocr_sync, path))
        except Exception as e:
            logging.warning(f"analyze fail: {e}")
        finally:
            if path and os.path.exists(path):
                os.remove(path)
    return worst, " ".join(ocr_parts)

def found_banned_words(text: str) -> list:
    low = text.lower()
    found = [w for w in BANNED_WORDS if w in low]
    found += [w for w in SEXUAL_WORDS if w in low]
    return found

def text_verdict(text: str) -> str:
    """'violation' | 'link' | 'clean'"""
    if found_banned_words(text):
        return "violation"
    if URL_RE.search(text) or DOMAIN_RE.search(text):
        return "link"
    return "clean"


async def notify_admin(text: str, kb=None):
    target = MOD_CHAT_ID if MOD_CHAT_ID else (next(iter(ADMIN_IDS)) if ADMIN_IDS else None)
    if not target:
        return
    try:
        await bot.send_message(target, text, reply_markup=kb)
    except Exception as e:
        logging.warning(f"notify_admin fail: {e}")


async def add_strike(uid: int, reason: str, detail: str = ""):
    """Засчитывает нарушение; на MAX_STRIKES -> бан с предложением разбана."""
    u = await get_user(uid)
    strikes = (u["strikes"] or 0) + 1
    body = f"Причина: {esc(reason)}"
    if detail:
        body += f"\n{esc(detail)}"
    if strikes >= MAX_STRIKES:
        await db.execute("UPDATE users SET status='banned', strikes=?, reject_reason=? WHERE uid=?",
                         (strikes, reason, uid))
        await db.commit()
        invalidate(uid)
        await bot.send_message(
            uid,
            f"⛔ <b>Вы заблокированы</b>\n{LINE}\n{body}\n"
            f"Это было {MAX_STRIKES}-е нарушение.\n\n"
            f"Снять блокировку можно за {UNBAN_PRICE} ⭐.",
            reply_markup=unban_kb())
    else:
        left = MAX_STRIKES - strikes
        await db.execute("UPDATE users SET status='rejected', strikes=?, reject_reason=? WHERE uid=?",
                         (strikes, reason, uid))
        await db.commit()
        invalidate(uid)
        await bot.send_message(
            uid,
            f"❌ <b>Анкета не прошла модерацию</b>\n{LINE}\n{body}\n"
            f"⚠️ Осталось попыток: <b>{left}</b> (потом блокировка).\n\n"
            f"Исправь анкету через «✏️ Изменить».\n"
            f"Считаешь, что это ошибка? Подай на пересмотр 👇",
            reply_markup=appeal_only_kb())


async def run_moderation(uid: int):
    """Полностью автоматическая модерация. Ничего одобрять вручную не нужно."""
    u = await get_user(uid)
    if not u:
        return
    photos = photos_of(u)
    nsfw, ocr = await analyze_photos(photos)
    about = u["about"] or ""

    # 1) текст в анкете
    about_words = found_banned_words(about)
    # 2) текст на фото (OCR)
    ocr_words = found_banned_words(ocr) if ocr else []

    # --- нарушения (в счётчик) ---
    if nsfw == "unsafe":
        await add_strike(uid, "на вашем фото обнаружен контент 18+")
        return
    if about_words:
        words = ", ".join(sorted(set(about_words))[:5])
        await add_strike(uid, "запрещённые слова в описании анкеты", f"Найдено: {words}")
        return
    if ocr_words:
        await add_strike(uid, "на вашем фото обнаружен запрещённый текст (18+/мат)")
        return

    # --- ссылки (отказ БЕЗ счётчика) ---
    about_link = bool(URL_RE.search(about) or DOMAIN_RE.search(about))
    ocr_link = bool(ocr and (URL_RE.search(ocr) or DOMAIN_RE.search(ocr)))
    if about_link or ocr_link:
        where = "на вашем фото" if (ocr_link and not about_link) else "в описании анкеты"
        await db.execute("UPDATE users SET status='rejected', reject_reason=? WHERE uid=?",
                         (f"ссылки запрещены ({where})", uid))
        await db.commit(); invalidate(uid)
        await bot.send_message(
            uid,
            f"❌ <b>Анкета не прошла модерацию</b>\n{LINE}\n"
            f"Обнаружена ссылка {where}. Ссылки запрещены.\n"
            "Упоминание вида <code>@username</code> — можно 🙂\n\n"
            "Поправь через «✏️ Изменить».")
        return

    # --- фото не удалось проверить (нет модели / серая зона) -> публикуем,
    #     полагаемся на жалобы пользователей ---
    await db.execute("UPDATE users SET status='active', reject_reason='' WHERE uid=?", (uid,))
    await db.commit(); invalidate(uid)
    await bot.send_message(uid, "✅ <b>Анкета одобрена и опубликована!</b>\n"
                                "Жми «🔍 Смотреть анкеты» 💞", reply_markup=main_menu())


# ==================== REGISTRATION / EDIT ====================
@dp.message(CommandStart())
async def start(m: Message, state: FSMContext):
    await state.clear()
    u = await get_user(m.from_user.id)
    if u:
        await m.answer("👋 <b>С возвращением!</b>\nЧем займёмся?", reply_markup=main_menu())
    else:
        # реферальная ссылка: /start ref12345
        parts = (m.text or "").split(maxsplit=1)
        if len(parts) == 2 and parts[1].startswith("ref"):
            ref_id = parts[1][3:]
            if ref_id.isdigit() and int(ref_id) != m.from_user.id:
                PENDING_REF[m.from_user.id] = int(ref_id)
        await state.set_state(Reg.name)
        await m.answer(
            "✨ <b>Добро пожаловать в Симпа!</b> ✨\n"
            f"{LINE}\n"
            "Здесь живут новые знакомства 💞\n"
            "Создадим твою анкету за минуту.\n\n"
            "Для начала — <b>как тебя зовут?</b>",
            reply_markup=ReplyKeyboardRemove())

@dp.message(Command("edit"))
@dp.message(F.text == "✏️ Изменить")
async def edit_start(m: Message, state: FSMContext):
    await state.set_state(Reg.name)
    await m.answer("✏️ Заполним анкету заново.\n\n<b>Как тебя зовут?</b>", reply_markup=ReplyKeyboardRemove())

@dp.message(Reg.name)
async def reg_name(m: Message, state: FSMContext):
    if not m.text:
        return await m.answer("Введи имя текстом 🙂")
    await state.update_data(name=m.text.strip()[:40])
    await state.set_state(Reg.age)
    await m.answer("Отлично! Сколько тебе <b>лет</b>?")

@dp.message(Reg.age)
async def reg_age(m: Message, state: FSMContext):
    if not m.text or not m.text.isdigit() or not (14 <= int(m.text) <= 99):
        return await m.answer("Введи возраст числом от 14 до 99.")
    await state.update_data(age=int(m.text))
    await state.set_state(Reg.gender)
    await m.answer("Твой <b>пол</b>:", reply_markup=gender_kb())

@dp.callback_query(Reg.gender, F.data.startswith("g_"))
async def reg_gender(c: CallbackQuery, state: FSMContext):
    await state.update_data(gender=c.data.split("_")[1])
    await state.set_state(Reg.looking)
    await c.message.edit_text("Кого ты <b>ищешь</b>?", reply_markup=looking_kb())
    await c.answer()

@dp.callback_query(Reg.looking, F.data.startswith("l_"))
async def reg_looking(c: CallbackQuery, state: FSMContext):
    await state.update_data(looking=c.data.split("_")[1])
    await state.set_state(Reg.about)
    await c.message.edit_text("Расскажи <b>о себе</b> — пару предложений, чтобы зацепить 😉")
    await c.answer()

@dp.message(Reg.about)
async def reg_about(m: Message, state: FSMContext):
    if not m.text:
        return await m.answer("Напиши немного текста о себе.")
    await state.update_data(about=m.text.strip()[:400], photos=[])
    await state.set_state(Reg.photos)
    await m.answer(f"📸 Теперь пришли свои фото (до {MAX_PHOTOS}).\nКогда хватит — жми «Готово».",
                   reply_markup=photos_done_kb(0))

@dp.message(Reg.photos, F.photo)
async def reg_photos(m: Message, state: FSMContext):
    d = await state.get_data()
    ph = d.get("photos", [])
    if len(ph) >= MAX_PHOTOS:
        return await m.answer("Уже максимум фото. Жми «Готово».", reply_markup=photos_done_kb(len(ph)))
    ph.append(m.photo[-1].file_id)
    await state.update_data(photos=ph)
    if len(ph) >= MAX_PHOTOS:
        await m.answer("📸 Максимум набран!", reply_markup=photos_done_kb(len(ph)))
    else:
        await m.answer(f"✅ Фото {len(ph)}/{MAX_PHOTOS} добавлено.", reply_markup=photos_done_kb(len(ph)))

@dp.message(Reg.photos)
async def reg_photos_wrong(m: Message, state: FSMContext):
    d = await state.get_data()
    await m.answer("Нужно именно фото 📸", reply_markup=photos_done_kb(len(d.get("photos", []))))

@dp.callback_query(Reg.photos, F.data == "ph_done")
async def reg_photos_done(c: CallbackQuery, state: FSMContext):
    d = await state.get_data()
    if not d.get("photos"):
        return await c.answer("Добавь хотя бы одно фото 📸", show_alert=True)
    await state.set_state(Reg.location)
    try:
        await c.message.delete()
    except Exception:
        pass
    await c.message.answer(
        "📍 <b>Последний шаг — геолокация</b>\n"
        "Она нужна, чтобы показывать тебе людей рядом и тебя — соседям.\n"
        "Нажми кнопку ниже 👇",
        reply_markup=loc_kb())
    await c.answer()

@dp.message(Reg.location, F.location)
async def reg_loc(m: Message, state: FSMContext):
    await state.update_data(lat=m.location.latitude, lon=m.location.longitude)
    await finalize(m, state)

@dp.message(Reg.location)
async def reg_loc_other(m: Message):
    await m.answer("📍 Геолокация обязательна для подбора рядом.\nНажми кнопку «📍 Отправить геолокацию».",
                   reply_markup=loc_kb())

async def finalize(m: Message, state: FSMContext):
    d = await state.get_data()
    uid = m.from_user.id
    existed = await get_user(uid)
    created = existed["created"] if existed else now()
    is_new = existed is None
    keep = dict(strikes=0, top_tier=0, top_until=0, boost_until=0, likes_until=0,
                f_age_min=14, f_age_max=99, f_dist=0,
                referrer=0, ref_count=0, ref_progress=0)
    if existed:
        for k in keep:
            keep[k] = existed[k]
    # реферер (только для новой анкеты и если пришёл по ссылке)
    if is_new and uid in PENDING_REF:
        keep["referrer"] = PENDING_REF.pop(uid)
    await db.execute("""INSERT OR REPLACE INTO users
        (uid,name,age,gender,looking,about,photos,lat,lon,status,reject_reason,
         strikes,top_tier,top_until,boost_until,likes_until,f_age_min,f_age_max,f_dist,
         referrer,ref_count,ref_progress,created)
        VALUES(?,?,?,?,?,?,?,?,?, 'pending','', ?,?,?,?,?,?,?,?,?,?,?,?)""",
        (uid, d["name"], d["age"], d["gender"], d["looking"], d["about"],
         json.dumps(d["photos"]), d.get("lat"), d.get("lon"),
         keep["strikes"], keep["top_tier"], keep["top_until"], keep["boost_until"], keep["likes_until"],
         keep["f_age_min"], keep["f_age_max"], keep["f_dist"],
         keep["referrer"], keep["ref_count"], keep["ref_progress"], created))
    await db.commit()
    await state.clear()
    invalidate(uid)
    await m.answer("🎉 <b>Анкета готова!</b>\nПроверяю её…", reply_markup=main_menu())
    await run_moderation(uid)
    # начислить приглашение рефереру (один раз, для новой анкеты)
    if is_new and keep["referrer"]:
        await credit_referral(keep["referrer"])


async def credit_referral(ref_uid: int):
    """+1 приглашённый рефереру; за каждые REF_NEEDED — день ⭐ Премиума."""
    ref = await get_user(ref_uid)
    if not ref:
        return
    count = (ref["ref_count"] or 0) + 1
    progress = (ref["ref_progress"] or 0) + 1
    reward_msg = ""
    if progress >= REF_NEEDED:
        progress = 0
        # выдать день Премиума (продлевает, если уже есть; не понижает Супер/VIP)
        base = max(now(), ref["top_until"] or 0)
        until = base + REF_REWARD_DAYS * 86400
        new_tier = ref["top_tier"] if (top_active(ref) and ref["top_tier"] >= 1) else 1
        await db.execute("UPDATE users SET ref_count=?, ref_progress=?, top_tier=?, top_until=? WHERE uid=?",
                         (count, progress, new_tier, until, ref_uid))
        reward_msg = (f"\n🎁 Ты пригласил {REF_NEEDED} друзей — "
                      f"тебе начислен {REF_REWARD_DAYS} день ⭐ Премиума до {fmt_dt(until)}!")
    else:
        left = REF_NEEDED - progress
        await db.execute("UPDATE users SET ref_count=?, ref_progress=? WHERE uid=?",
                         (count, progress, ref_uid))
        reward_msg = f"\nЕщё {left} — и получишь день ⭐ Премиума 🔥"
    await db.commit()
    invalidate(ref_uid)
    try:
        await bot.send_message(ref_uid, f"🎉 По твоей ссылке зарегистрировался новый друг!\n"
                                        f"Всего приглашено: <b>{count}</b>.{reward_msg}")
    except Exception:
        pass


# ==================== BROWSING ====================
def cand_rank(viewer, r):
    if top_active(r):
        if r["top_tier"] == 3:
            tier = 0      # 👑 VIP — выше всех
        elif r["top_tier"] == 2:
            tier = 1      # 💎 Супер
        else:
            tier = 2      # ⭐ Премиум
    elif r["boost_until"] and r["boost_until"] > now():
        tier = 3          # 🚀 буст
    else:
        tier = 4          # обычные
    if viewer["lat"] is not None and r["lat"] is not None:
        d = haversine(viewer["lat"], viewer["lon"], r["lat"], r["lon"])
    else:
        d = 1e9
    return (tier, d)

async def refill_queue(uid: int):
    u = await get_user(uid)
    if not u:
        return
    gfilter = ""
    if u["looking"] == "m":
        gfilter = "AND gender='m'"
    elif u["looking"] == "f":
        gfilter = "AND gender='f'"
    q = f"""SELECT * FROM users
            WHERE uid != ? AND status='active' {gfilter}
              AND age BETWEEN ? AND ?
              AND uid NOT IN (SELECT whom FROM seen WHERE who=?)
            LIMIT ?"""
    cur = await db.execute(q, (uid, u["f_age_min"], u["f_age_max"], uid, BATCH))
    rows = list(await cur.fetchall())
    if u["f_dist"] and u["lat"] is not None:
        rows = [r for r in rows if r["lat"] is not None and
                haversine(u["lat"], u["lon"], r["lat"], r["lon"]) <= u["f_dist"]]
    rows.sort(key=lambda r: cand_rank(u, r))
    QUEUE[uid] = deque(rows)

async def next_candidate(uid: int):
    if not QUEUE[uid]:
        await refill_queue(uid)
    if QUEUE[uid]:
        return QUEUE[uid].popleft()
    return None

def _history_get(uid: int):
    """Вернуть валидную историю (с учётом TTL) или None."""
    h = SWIPE_HISTORY.get(uid)
    if not h:
        return None
    if time.time() - h.get("ts", 0) > HISTORY_TTL:
        SWIPE_HISTORY.pop(uid, None)
        return None
    return h

def _history_push(uid: int, row):
    """Добавить анкету в историю (максимум HISTORY_MAX, старые выпадают)."""
    h = _history_get(uid) or {"items": [], "ts": time.time()}
    # не дублируем подряд один и тот же uid
    h["items"] = [r for r in h["items"] if r["uid"] != row["uid"]]
    h["items"].append(row)
    if len(h["items"]) > HISTORY_MAX:
        h["items"] = h["items"][-HISTORY_MAX:]
    h["ts"] = time.time()
    SWIPE_HISTORY[uid] = h

async def show_next(chat_id: int, uid: int, save_history: bool = True):
    # сохраняем текущую анкету в историю перед показом следующей
    if save_history:
        cur_state = CURRENT.get(uid)
        if cur_state and cur_state.get("row"):
            _history_push(uid, cur_state["row"])
    cand = await next_candidate(uid)
    if not cand:
        CURRENT.pop(uid, None)
        return await bot.send_message(chat_id, "🔎 Анкеты пока закончились.\n"
                                               "Смягчи фильтры в «⚙️ Фильтры» или загляни попозже 🙂",
                                      reply_markup=main_menu())
    viewer = await get_user(uid)
    await db.execute("INSERT OR IGNORE INTO seen(who,whom) VALUES(?,?)", (uid, cand["uid"]))
    await db.commit()
    ph = photos_of(cand)
    has_back = bool(_history_get(uid) and _history_get(uid)["items"])
    msg = await bot.send_photo(chat_id, ph[0],
                               caption=profile_caption(cand, viewer),
                               reply_markup=swipe_kb(cand["uid"], len(ph), has_back=has_back))
    CURRENT[uid] = {"row": cand, "idx": 0, "msg": msg.message_id, "chat": chat_id}

@dp.message(F.text == "🔍 Смотреть анкеты")
async def browse(m: Message):
    u = await get_user(m.from_user.id)
    if not u:
        return await m.answer("Сначала создай анкету: /start")
    if u["status"] == "pending":
        await m.answer("🕓 Твоя анкета ещё на модерации — но смотреть других уже можно 🙂")
    await show_next(m.chat.id, m.from_user.id)

@dp.callback_query(F.data.in_({"pprev", "pnext"}))
async def flip_photo(c: CallbackQuery):
    st = CURRENT.get(c.from_user.id)
    if not st:
        return await c.answer()
    ph = photos_of(st["row"])
    if len(ph) <= 1:
        return await c.answer()
    st["idx"] = (st["idx"] + (1 if c.data == "pnext" else -1)) % len(ph)
    viewer = await get_user(c.from_user.id)
    has_back = bool(_history_get(c.from_user.id) and _history_get(c.from_user.id)["items"])
    kb = swipe_kb(st["row"]["uid"], len(ph), has_back=has_back)
    kb.inline_keyboard[0][1].text = f"{st['idx']+1}/{len(ph)}"
    try:
        await bot.edit_message_media(
            InputMediaPhoto(media=ph[st["idx"]], caption=profile_caption(st["row"], viewer)),
            chat_id=st["chat"], message_id=st["msg"], reply_markup=kb)
    except Exception:
        pass
    await c.answer()

@dp.callback_query(F.data == "noop")
async def noop(c: CallbackQuery):
    await c.answer()


def swipe_allowed(uid: int) -> Optional[str]:
    t = time.time()
    if t - SWIPE_TS.get(uid, 0) < SWIPE_MIN_INTERVAL:
        return "Не так быстро 🙂"
    cnt, day = SWIPE_DAY[uid]
    if t - day > 86400:
        SWIPE_DAY[uid] = [0, t]; cnt = 0
    if cnt >= SWIPE_DAILY_LIMIT:
        return "На сегодня хватит свайпов 😴 Возвращайся завтра!"
    SWIPE_TS[uid] = t
    SWIPE_DAY[uid][0] = cnt + 1
    return None

async def do_like(me: int, target: int, message: str = "") -> bool:
    """Ставит лайк, возвращает True если это метч."""
    await db.execute("INSERT OR IGNORE INTO likes(who,whom,ts) VALUES(?,?,?)", (me, target, now()))
    cur = await db.execute("SELECT 1 FROM likes WHERE who=? AND whom=?", (target, me))
    match = await cur.fetchone()
    await db.commit()
    if match:
        await notify_match(me, target)
    else:
        await notify_like(me, target, message)
    return bool(match)

@dp.callback_query(F.data.startswith("like_"))
async def like(c: CallbackQuery):
    warn = swipe_allowed(c.from_user.id)
    if warn:
        return await c.answer(warn, show_alert=True)
    target = int(c.data.split("_")[1])
    await do_like(c.from_user.id, target)
    await c.answer("❤️")
    await show_next(c.message.chat.id, c.from_user.id)

@dp.callback_query(F.data.startswith("likemsg_"))
async def like_msg(c: CallbackQuery):
    warn = swipe_allowed(c.from_user.id)
    if warn:
        return await c.answer(warn, show_alert=True)
    target = int(c.data.split("_")[1])
    PENDING_MSG[c.from_user.id] = target
    await c.answer()
    await c.message.answer(
        f"💌 Напиши короткое сообщение (до {MSG_LIMIT} символов).\n"
        "Оно придёт вместе с твоим лайком.\n"
        "<i>Или нажми «🔍 Смотреть анкеты», чтобы отменить.</i>")

@dp.callback_query(F.data == "appeal_start")
async def appeal_start(c: CallbackQuery):
    uid = c.from_user.id
    u = await get_user(uid)
    if not u or u["status"] not in ("rejected", "banned"):
        return await c.answer("Пересмотр доступен только для отклонённой или заблокированной анкеты.", show_alert=True)
    # уже подавал?
    ex = await (await db.execute("SELECT 1 FROM appeals WHERE uid=?", (uid,))).fetchone()
    if ex:
        return await c.answer("Вы уже подали на пересмотр. Дождитесь решения администратора.", show_alert=True)
    APPEAL_WAIT.add(uid)
    await c.answer()
    await c.message.answer(
        "🛟 <b>Пересмотр модерации</b>\n"
        f"{LINE}\n"
        "Опиши коротко, почему считаешь блокировку ошибкой (до 300 символов).\n"
        "Администратор проверит вручную.")

@dp.message(F.text, lambda m: m.from_user.id in APPEAL_WAIT)
async def appeal_text(m: Message):
    uid = m.from_user.id
    APPEAL_WAIT.discard(uid)
    text = (m.text or "").strip()[:300]
    await db.execute("INSERT OR REPLACE INTO appeals(uid,text,ts) VALUES(?,?,?)", (uid, text, now()))
    await db.commit()
    await m.answer("✅ Заявка на пересмотр отправлена. Дождись решения администратора 🙏")
    u = await get_user(uid)
    ph = photos_of(u) if u else []
    cap = (f"🛟 <b>Апелляция (пересмотр)</b>\nID: <code>{uid}</code>\n"
           f"Статус: {u['status'] if u else '?'}\n"
           f"Причина блокировки: {esc(u['reject_reason']) if u and u['reject_reason'] else '—'}\n"
           f"{LINE}\n"
           f"💬 Сообщение: «{esc(text)}»\n{LINE}\n"
           + (profile_caption(u) if u else ""))
    await broadcast_admins(cap, photo=(ph[0] if ph else None), kb=appeal_kb(uid))


@dp.message(F.text & ~F.text.startswith("/") & ~F.text.in_({
    "🔍 Смотреть анкеты", "👤 Моя анкета", "💞 Мои метчи", "❤️ Кто меня лайкнул",
    "🚀 Поднять анкету", "🎁 Пригласить друзей", "⚙️ Фильтры", "✏️ Изменить",
    "⏸ Скрыть/Показать", "🗑 Удалить"
}))
async def catch_like_message(m: Message, state: FSMContext):
    """Ловит текст сообщения для лайка (только если мы его ждём и не в другом сценарии)."""
    if await state.get_state() is not None:
        return  # идёт регистрация/фильтр — не вмешиваемся
    target = PENDING_MSG.get(m.from_user.id)
    if not target:
        return  # обычный текст вне сценария — игнор
    PENDING_MSG.pop(m.from_user.id, None)
    text = (m.text or "").strip()
    if len(text) > MSG_LIMIT:
        return await m.answer(f"Слишком длинно ({len(text)}/{MSG_LIMIT}). "
                              "Напиши покороче и снова нажми «💌 Лайк + сообщение».")
    tv = text_verdict(text)
    if tv == "violation":
        return await m.answer("❌ В сообщении есть запрещённые слова. Лайк не отправлен.")
    if tv == "link":
        return await m.answer("❌ В сообщении нельзя ссылки. Лайк не отправлен.")
    target_user = await get_user(target)
    if not target_user or target_user["status"] != "active":
        return await m.answer("Эта анкета уже недоступна.")
    match = await do_like(m.from_user.id, target, text)
    if match:
        await m.answer("🎉 Это сразу метч! Можете писать друг другу.", reply_markup=main_menu())
    else:
        await m.answer("💌 Лайк с сообщением отправлен!", reply_markup=main_menu())
    await show_next(m.chat.id, m.from_user.id)

@dp.callback_query(F.data.startswith("dislike_"))
async def dislike(c: CallbackQuery):
    warn = swipe_allowed(c.from_user.id)
    if warn:
        return await c.answer(warn, show_alert=True)
    await c.answer("👎")
    await show_next(c.message.chat.id, c.from_user.id)

@dp.callback_query(F.data == "stop")
async def stop_browse(c: CallbackQuery):
    CURRENT.pop(c.from_user.id, None)
    NEARBY_NOTIFIED.discard(c.from_user.id)
    PENDING_MSG.pop(c.from_user.id, None)
    SWIPE_HISTORY.pop(c.from_user.id, None)
    await c.answer()
    await c.message.answer("Окей, до встречи 🙂", reply_markup=main_menu())

@dp.callback_query(F.data == "goback")
async def go_back(c: CallbackQuery):
    """Вернуться к предыдущей анкете (до 3 назад, живёт 30 мин)."""
    uid = c.from_user.id
    h = _history_get(uid)
    if not h or not h["items"]:
        return await c.answer("Предыдущих анкет нет 🙂", show_alert=True)
    prev = h["items"].pop()           # последняя из истории
    h["ts"] = time.time()
    if not h["items"]:
        SWIPE_HISTORY.pop(uid, None)  # история опустела
    # проверим, что анкета ещё активна
    fresh = await get_user(prev["uid"])
    if not fresh or fresh["status"] != "active":
        await c.answer("Эта анкета уже недоступна", show_alert=True)
        # покажем следующую по истории, если есть
        if _history_get(uid) and _history_get(uid)["items"]:
            return await go_back(c)
        return
    viewer = await get_user(uid)
    ph = photos_of(fresh)
    has_back = bool(_history_get(uid) and _history_get(uid)["items"])
    await c.answer("⬅️ Предыдущая")
    msg = await bot.send_photo(c.message.chat.id, ph[0],
                               caption=profile_caption(fresh, viewer),
                               reply_markup=swipe_kb(fresh["uid"], len(ph), has_back=has_back))
    CURRENT[uid] = {"row": fresh, "idx": 0, "msg": msg.message_id, "chat": c.message.chat.id}


async def user_link(uid: int) -> str:
    try:
        chat = await bot.get_chat(uid)
        if chat.username:
            return f"@{chat.username}"
    except Exception:
        pass
    return f'<a href="tg://user?id={uid}">профиль</a>'

async def notify_like(me: int, target: int, message: str = ""):
    """Уведомление о входящем лайке (без взаимности)."""
    liker = await get_user(me)
    if not liker:
        return
    extra = ""
    if message:
        extra = f"\n💌 Сообщение: «{esc(message)}»"
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="❤️ Посмотреть, кто лайкнул", callback_data="open_likes")
    ]])
    try:
        await bot.send_message(
            target,
            f"❤️ <b>Тебя кто-то лайкнул!</b>{extra}\n\n"
            "Ответь взаимностью, чтобы открыть чат 💞",
            reply_markup=kb)
    except Exception:
        pass

async def notify_match(a: int, b: int):
    ua, ub = await get_user(a), await get_user(b)
    try:
        await bot.send_message(
            a, f"🎉💞 <b>Это взаимно!</b> 💞🎉\n{LINE}\n"
               f"Вы с <b>{esc(ub['name'])}</b> понравились друг другу!\n"
               f"Напиши первым 👉 {await user_link(b)}")
    except Exception:
        pass
    try:
        await bot.send_message(
            b, f"🎉💞 <b>Это взаимно!</b> 💞🎉\n{LINE}\n"
               f"Вы с <b>{esc(ua['name'])}</b> понравились друг другу!\n"
               f"Напиши первым 👉 {await user_link(a)}")
    except Exception:
        pass


# ==================== MATCHES / WHO LIKED ====================
@dp.message(F.text == "💞 Мои метчи")
async def my_matches(m: Message):
    uid = m.from_user.id
    cur = await db.execute("""
        SELECT u.* FROM likes l1
        JOIN likes l2 ON l1.whom=l2.who AND l1.who=l2.whom
        JOIN users u ON u.uid=l1.whom
        WHERE l1.who=? ORDER BY l1.ts DESC LIMIT 50""", (uid,))
    rows = await cur.fetchall()
    if not rows:
        return await m.answer("💞 Пока нет взаимных симпатий.\nЛайкай активнее — всё впереди 😉")
    lines = [f"• <b>{esc(r['name'])}</b>, {r['age']} — {await user_link(r['uid'])}" for r in rows]
    await m.answer(f"💞 <b>Твои метчи</b>\n{LINE}\n" + "\n".join(lines))

@dp.callback_query(F.data == "open_likes")
async def open_likes_cb(c: CallbackQuery):
    await c.answer()
    await _show_who_liked(c.from_user.id, c.message.chat.id)

@dp.message(F.text == "❤️ Кто меня лайкнул")
async def who_liked(m: Message):
    await _show_who_liked(m.from_user.id, m.chat.id)

async def _show_who_liked(uid: int, chat_id: int):
    u = await get_user(uid)
    if not u:
        return await bot.send_message(chat_id, "Сначала создай анкету: /start")
    cur = await db.execute("""
        SELECT u.* FROM likes l
        JOIN users u ON u.uid=l.who
        WHERE l.whom=? AND u.status='active'
          AND NOT EXISTS (SELECT 1 FROM likes l2 WHERE l2.who=? AND l2.whom=l.who)
          AND l.who NOT IN (SELECT whom FROM seen WHERE who=?)
        ORDER BY l.ts DESC LIMIT 30""", (uid, uid, uid))
    rows = await cur.fetchall()
    n = len(rows)
    if n == 0:
        return await bot.send_message(chat_id, "❤️ Пока новых лайков нет.\nЭто скоро изменится 😉")
    await bot.send_message(chat_id, f"❤️ <b>Тебя лайкнули: {n}</b>\nЛайкни в ответ — и будет метч 💞")
    for r in rows:
        ph = photos_of(r)
        kb = InlineKeyboardMarkup(inline_keyboard=[[
            InlineKeyboardButton(text="❤️ В ответ", callback_data=f"wllike_{r['uid']}"),
            InlineKeyboardButton(text="👎", callback_data=f"wlskip_{r['uid']}"),
        ]])
        await bot.send_photo(chat_id, ph[0], caption=profile_caption(r, u), reply_markup=kb)

@dp.callback_query(F.data.startswith("wllike_"))
async def wl_like(c: CallbackQuery):
    """Лайк в ответ из списка 'кто меня лайкнул' — карточка исчезает, лента не открывается."""
    target = int(c.data.split("_")[1])
    match = await do_like(c.from_user.id, target)
    try:
        await c.message.delete()
    except Exception:
        try:
            await c.message.edit_reply_markup(reply_markup=None)
        except Exception:
            pass
    if match:
        await c.answer("🎉 Это метч!", show_alert=True)
    else:
        await c.answer("❤️")

@dp.callback_query(F.data.startswith("wlskip_"))
async def wl_skip(c: CallbackQuery):
    target = int(c.data.split("_")[1])
    # запоминаем, что отклонили — больше не покажется в списке лайкнувших
    await db.execute("INSERT OR IGNORE INTO seen(who,whom) VALUES(?,?)", (c.from_user.id, target))
    await db.commit()
    try:
        await c.message.delete()
    except Exception:
        try:
            await c.message.edit_reply_markup(reply_markup=None)
        except Exception:
            pass
    await c.answer("Пропущено")

@dp.callback_query(F.data == "wl_skip")
async def wl_skip_old(c: CallbackQuery):
    """Старый формат кнопки (для карточек, отправленных до обновления)."""
    try:
        await c.message.delete()
    except Exception:
        pass
    await c.answer("Пропущено")


# ==================== PROFILE / PAUSE / DELETE ====================
@dp.message(F.text == "👤 Моя анкета")
async def my_profile(m: Message):
    u = await get_user(m.from_user.id)
    if not u:
        return await m.answer("Анкеты нет. /start")
    likes_cnt = (await (await db.execute("SELECT COUNT(*) c FROM likes WHERE whom=?", (m.from_user.id,))).fetchone())["c"]
    views_cnt = (await (await db.execute("SELECT COUNT(*) c FROM seen WHERE whom=?", (m.from_user.id,))).fetchone())["c"]
    ph = photos_of(u)
    cap = own_profile_caption(u) + f"\n{LINE}\n📊 Просмотров: <b>{views_cnt}</b> · Лайков: <b>{likes_cnt}</b>"
    if ph:
        await m.answer_photo(ph[0], caption=cap, reply_markup=main_menu())
    else:
        await m.answer(cap, reply_markup=main_menu())

@dp.message(F.text == "⏸ Скрыть/Показать")
async def toggle_pause(m: Message):
    u = await get_user(m.from_user.id)
    if not u:
        return await m.answer("Анкеты нет. /start")
    if u["status"] == "active":
        await db.execute("UPDATE users SET status='paused' WHERE uid=?", (m.from_user.id,))
        await db.commit()
        await m.answer("⏸ <b>Анкета скрыта</b> — тебя не показывают.\nНажми снова, чтобы вернуть.")
    elif u["status"] == "paused":
        await db.execute("UPDATE users SET status='active' WHERE uid=?", (m.from_user.id,))
        await db.commit()
        await m.answer("▶️ <b>Анкета снова видна!</b>")
    else:
        await m.answer(f"Сейчас статус: {u['status']}. Пауза доступна только для опубликованной анкеты.")

@dp.message(F.text == "🗑 Удалить")
async def delete_profile(m: Message):
    uid = m.from_user.id
    await db.execute("DELETE FROM users WHERE uid=?", (uid,))
    await db.execute("DELETE FROM likes WHERE who=? OR whom=?", (uid, uid))
    await db.execute("DELETE FROM seen WHERE who=? OR whom=?", (uid, uid))
    await db.execute("DELETE FROM reports WHERE who=? OR whom=?", (uid, uid))
    await db.commit()
    invalidate(uid)
    CURRENT.pop(uid, None)
    await m.answer("🗑 Анкета удалена.\n/start — создать заново.", reply_markup=ReplyKeyboardRemove())


# ==================== FILTERS ====================
@dp.message(F.text == "⚙️ Фильтры")
async def filters_menu(m: Message):
    u = await get_user(m.from_user.id)
    if not u:
        return await m.answer("Сначала создай анкету: /start")
    await m.answer("⚙️ <b>Фильтры подбора</b>\nПо умолчанию показываю людей рядом с тобой.\nНастрой при желании:",
                   reply_markup=filters_kb(u))

@dp.callback_query(F.data == "f_age")
async def f_age(c: CallbackQuery, state: FSMContext):
    await state.set_state(Filt.age)
    await c.message.answer("Введи диапазон возраста через дефис, напр. <code>18-30</code>:")
    await c.answer()

@dp.message(Filt.age)
async def f_age_set(m: Message, state: FSMContext):
    mt = re.match(r"^\s*(\d{1,2})\s*-\s*(\d{1,3})\s*$", m.text or "")
    if not mt:
        return await m.answer("Формат: <code>18-30</code>")
    a, b = int(mt.group(1)), int(mt.group(2))
    a, b = max(14, min(a, b)), min(99, max(a, b))
    await db.execute("UPDATE users SET f_age_min=?, f_age_max=? WHERE uid=?", (a, b, m.from_user.id))
    await db.commit()
    invalidate(m.from_user.id)
    await state.clear()
    u = await get_user(m.from_user.id)
    await m.answer(f"✅ Возраст: {a}–{b}", reply_markup=filters_kb(u))

@dp.callback_query(F.data == "f_dist")
async def f_dist(c: CallbackQuery):
    await c.message.answer("Максимальный радиус поиска:", reply_markup=dist_kb())
    await c.answer()

@dp.callback_query(F.data.startswith("dist_"))
async def f_dist_set(c: CallbackQuery):
    d = int(c.data.split("_")[1])
    await db.execute("UPDATE users SET f_dist=? WHERE uid=?", (d, c.from_user.id))
    await db.commit()
    invalidate(c.from_user.id)
    await c.message.edit_text(f"✅ Радиус: {'не важно' if not d else str(d)+' км'}")
    await c.answer()

@dp.callback_query(F.data == "f_reset")
async def f_reset(c: CallbackQuery):
    await db.execute("UPDATE users SET f_age_min=14, f_age_max=99, f_dist=0 WHERE uid=?",
                     (c.from_user.id,))
    await db.commit()
    invalidate(c.from_user.id)
    u = await get_user(c.from_user.id)
    await c.message.edit_text("♻️ Фильтры сброшены.", reply_markup=filters_kb(u))
    await c.answer()


# ==================== REPORTS (3 от разных -> скрытие -> тайная проверка) ====================
@dp.callback_query(F.data.startswith("report_"))
async def report(c: CallbackQuery):
    me = c.from_user.id
    target = int(c.data.split("_")[1])
    if me == target:
        return await c.answer("Нельзя пожаловаться на себя 🙂", show_alert=True)

    # --- дневной лимит жалоб (скользящие 24 часа) ---
    reporter = await get_user(me)
    if reporter:
        win = reporter["report_window"] or 0
        cnt_today = reporter["report_count"] or 0
        # окно истекло (прошло 24ч) -> сброс
        if now() - win >= 86400:
            cnt_today = 0
            win = now()
            await db.execute("UPDATE users SET report_count=0, report_window=? WHERE uid=?", (win, me))
            await db.commit()
        if cnt_today >= DAILY_REPORTS:
            left = 86400 - (now() - win)
            h = left // 3600
            m_ = (left % 3600) // 60
            return await c.answer(
                f"❌ У вас закончились жалобы на сегодня ({DAILY_REPORTS}/{DAILY_REPORTS}).\n"
                f"Попробуйте через {h:02d}:{m_:02d}.",
                show_alert=True)

    # проверка: уже жаловался на этого?
    already = await (await db.execute("SELECT 1 FROM reports WHERE who=? AND whom=?", (me, target))).fetchone()

    await db.execute("INSERT OR IGNORE INTO reports(who,whom,ts) VALUES(?,?,?)", (me, target, now()))
    # засчитываем в дневной лимит ТОЛЬКО новую жалобу (не повторную на того же)
    if not already and reporter:
        new_win = reporter["report_window"] or now()
        if now() - new_win >= 86400:
            new_win = now()
        await db.execute("UPDATE users SET report_count=report_count+1, report_window=? WHERE uid=?",
                         (new_win, me))
    await db.commit()

    # уникальные жалобщики
    cnt = (await (await db.execute("SELECT COUNT(DISTINCT who) c FROM reports WHERE whom=?", (target,))).fetchone())["c"]
    if cnt >= REPORTS_TO_HIDE:
        tu = await get_user(target)
        if tu and tu["status"] == "active":
            await db.execute("UPDATE users SET status='hidden' WHERE uid=?", (target,))
            await db.commit()
            invalidate(target)
            try:
                await bot.send_message(
                    target,
                    "🚫 <b>Ваша анкета временно скрыта</b>\n"
                    "На неё поступили жалобы, и она отправлена на проверку администратору.\n"
                    "Дождитесь решения — обычно это занимает немного времени.")
            except Exception:
                pass
            ph = photos_of(tu)
            cap = (f"🚩 <b>Жалобы на анкету</b> (×{cnt})\nID: <code>{target}</code>\n{LINE}\n"
                   + profile_caption(tu))
            await broadcast_admins(cap, photo=(ph[0] if ph else None), kb=review_kb(target))
    # сколько жалоб осталось сегодня
    r2 = await get_user(me)
    left_today = max(0, DAILY_REPORTS - (r2["report_count"] or 0)) if r2 else 0
    await c.answer(f"🚩 Жалоба отправлена. Спасибо!\nОсталось жалоб сегодня: {left_today}", show_alert=True)
    await show_next(c.message.chat.id, me)


# ==================== PAYMENTS (Telegram Stars) ====================
async def send_invoice(chat_id: int, title: str, desc: str, payload: str, amount: int):
    await bot.send_invoice(
        chat_id=chat_id, title=title, description=desc, payload=payload,
        provider_token="", currency="XTR",
        prices=[LabeledPrice(label=title, amount=amount)],
    )

@dp.message(F.text == "🎁 Пригласить друзей")
async def invite(m: Message):
    u = await get_user(m.from_user.id)
    if not u:
        return await m.answer("Сначала создай анкету: /start")
    link = f"https://t.me/{BOT_USERNAME}?start=ref{m.from_user.id}"
    count = u["ref_count"] or 0
    progress = u["ref_progress"] or 0
    left = REF_NEEDED - progress
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="📤 Поделиться ссылкой",
                             url=f"https://t.me/share/url?url={link}&text="
                                 f"Залетай в Симпа — знакомства рядом 💞")
    ]])
    await m.answer(
        "🎁 <b>Приглашай друзей — получай Премиум!</b>\n"
        f"{LINE}\n"
        f"За каждых <b>{REF_NEEDED}</b> друзей, создавших анкету, "
        f"тебе {REF_REWARD_DAYS} день ⭐ Премиума бесплатно.\n\n"
        f"👥 Приглашено: <b>{count}</b>\n"
        f"⏳ До награды осталось: <b>{left}</b>\n\n"
        f"Твоя ссылка:\n<code>{link}</code>\n\n"
        "Отправь её друзьям 👇",
        reply_markup=kb)

@dp.message(F.text == "🚀 Поднять анкету")
async def promo(m: Message):
    u = await get_user(m.from_user.id)
    if not u:
        return await m.answer("Сначала создай анкету: /start")
    note = ""
    if top_active(u):
        tier = "💎 Супер Премиум" if u["top_tier"] == 2 else "⭐ Премиум"
        note = f"\n\n⏳ Сейчас активен <b>{tier}</b> до {fmt_dt(u['top_until'])}.\nПродлить можно будет, когда закончится."
    await m.answer(
        "🚀 <b>Поднять анкету</b>\n"
        f"{LINE}\n"
        "Чем выше анкета — тем больше просмотров и лайков 💞\n\n"
        f"💎 <b>СУПЕР ПРЕМИУМ</b> · {SUPER_PRICE} ⭐\n"
        "Самый верх, над всеми. Значок 💎 на анкете.\n\n"
        f"⭐ <b>ПРЕМИУМ</b> · {MEDIUM_PRICE} ⭐\n"
        "Выше обычных анкет. Значок ⭐.\n\n"
        "⏱ Покупка — ровно на <b>24 часа</b>. Купить снова можно, когда текущий топ закончится."
        + note,
        reply_markup=promo_kb())

@dp.callback_query(F.data.in_({"buy_super", "buy_medium"}))
async def buy_top(c: CallbackQuery):
    u = await get_user(c.from_user.id)
    if not u:
        return await c.answer("Сначала создай анкету: /start", show_alert=True)
    if top_active(u):
        return await c.answer(
            f"⏳ Топ уже активен до {fmt_dt(u['top_until'])}.\n"
            "Продлить можно будет, когда он закончится.", show_alert=True)
    if c.data == "buy_super":
        await send_invoice(c.message.chat.id, "💎 Супер Премиум",
                           "Твоя анкета в самом верху на 24 часа.", "top_super", SUPER_PRICE)
    else:
        await send_invoice(c.message.chat.id, "⭐ Премиум",
                           "Твоя анкета выше обычных на 24 часа.", "top_medium", MEDIUM_PRICE)
    await c.answer()

@dp.callback_query(F.data == "buy_boost")
async def buy_boost(c: CallbackQuery):
    await send_invoice(c.message.chat.id, "🚀 Буст 30 мин", "30 минут в приоритете показа.", "boost", BOOST_PRICE)
    await c.answer()

@dp.callback_query(F.data == "buy_likes")
async def buy_likes(c: CallbackQuery):
    await send_invoice(c.message.chat.id, "❤️ Кто меня лайкнул",
                       "Доступ к списку лайкнувших на 7 дней.", "likes", LIKES_PRICE)
    await c.answer()

@dp.callback_query(F.data == "unban_pay")
async def unban_pay(c: CallbackQuery):
    u = await get_user(c.from_user.id)
    # нельзя купить разбан, пока анкета на проверке по жалобам
    if u and u["status"] == "hidden":
        return await c.answer("Ваша анкета на проверке у администратора. "
                              "Дождитесь решения — разбан пока недоступен.", show_alert=True)
    await send_invoice(c.message.chat.id, "Снятие блокировки",
                       "Разблокировка аккаунта и сброс нарушений.", "unban", UNBAN_PRICE)
    await c.answer()

@dp.pre_checkout_query()
async def pre_checkout(q: PreCheckoutQuery):
    await q.answer(ok=True)

@dp.message(F.successful_payment)
async def paid(m: Message):
    sp = m.successful_payment
    payload = sp.invoice_payload
    uid = m.from_user.id
    await db.execute("INSERT OR IGNORE INTO payments(charge_id,uid,amount,kind,ts) VALUES(?,?,?,?,?)",
                     (sp.telegram_payment_charge_id, uid, sp.total_amount, payload, now()))

    if payload == "top_super":
        until = now() + TOP_DURATION
        await db.execute("UPDATE users SET top_tier=2, top_until=? WHERE uid=?", (until, uid))
        await db.commit(); invalidate(uid)
        await m.answer(f"💎 <b>Супер Премиум активирован!</b>\n{LINE}\n"
                       f"Анкета в самом верху до <b>{fmt_dt(until)}</b> 🔥", reply_markup=main_menu())
    elif payload == "top_medium":
        until = now() + TOP_DURATION
        await db.execute("UPDATE users SET top_tier=1, top_until=? WHERE uid=?", (until, uid))
        await db.commit(); invalidate(uid)
        await m.answer(f"⭐ <b>Премиум активирован!</b>\n{LINE}\n"
                       f"Анкета выше обычных до <b>{fmt_dt(until)}</b> ✨", reply_markup=main_menu())
    elif payload == "boost":
        u = await get_user(uid)
        until = max(now(), u["boost_until"] or 0) + BOOST_SECONDS
        await db.execute("UPDATE users SET boost_until=? WHERE uid=?", (until, uid))
        await db.commit(); invalidate(uid)
        await m.answer(f"🚀 <b>Буст активен</b> до {fmt_dt(until)}!", reply_markup=main_menu())
    elif payload == "likes":
        until = now() + LIKES_SECONDS
        await db.execute("UPDATE users SET likes_until=? WHERE uid=?", (until, uid))
        await db.commit()
        await m.answer("🔓 <b>Список лайкнувших открыт на 7 дней!</b>\nЖми «❤️ Кто меня лайкнул».",
                       reply_markup=main_menu())
    elif payload == "unban":
        await db.execute("UPDATE users SET status='rejected', strikes=0, reject_reason='' WHERE uid=?", (uid,))
        await db.commit(); invalidate(uid)
        await m.answer("✅ <b>Блокировка снята!</b>\n"
                       "Нарушения обнулены. Обнови анкету через «✏️ Изменить» — "
                       "она снова пройдёт проверку и опубликуется.", reply_markup=main_menu())
    else:
        await db.commit()
        await m.answer("Оплата получена ✅")

@dp.message(Command("paysupport"))
async def paysupport(m: Message):
    await m.answer("💬 По вопросам оплаты и возвратов напиши администратору.")


# ==================== ADMIN ====================
@dp.callback_query(F.data.startswith("rev_"))
async def review_decision(c: CallbackQuery):
    """Решение админа по жалобам."""
    if not (is_admin(c.from_user.id) or (MOD_CHAT_ID and c.message.chat.id == MOD_CHAT_ID)):
        return await c.answer("Нет прав", show_alert=True)
    _, decision, uid_s = c.data.split("_")
    uid = int(uid_s)
    u = await get_user(uid)
    if not u:
        return await c.answer("Анкета уже удалена", show_alert=True)
    if decision == "ok":
        # жалобы напрасны — вернуть и обнулить жалобы
        await db.execute("UPDATE users SET status='active' WHERE uid=?", (uid,))
        await db.execute("DELETE FROM reports WHERE whom=?", (uid,))
        note = "\n\n✅ ВОЗВРАЩЕНА (жалобы напрасны)"
        try:
            await bot.send_message(uid, "✅ <b>Проверка завершена</b>\n"
                                        "Жалобы не подтвердились, ваша анкета снова видна 💞",
                                   reply_markup=main_menu())
        except Exception:
            pass
    else:
        # подтверждено — отклонить (теперь доступен платный разбан)
        await db.execute("UPDATE users SET status='rejected', reject_reason='нарушение по жалобам' WHERE uid=?", (uid,))
        await db.execute("DELETE FROM reports WHERE whom=?", (uid,))
        note = "\n\n❌ ОТКЛОНЕНА"
        try:
            await bot.send_message(
                uid,
                "❌ <b>Проверка завершена</b>\n"
                "Жалобы подтвердились, анкета отклонена.\n"
                "Вы можете исправить её через «✏️ Изменить» или, при блокировке, снять её за звёзды.")
        except Exception:
            pass
    await db.commit()
    invalidate(uid)
    try:
        if c.message.photo:
            await c.message.edit_caption(caption=(c.message.caption or "") + note)
        else:
            await c.message.edit_text((c.message.text or "") + note)
    except Exception:
        pass
    await c.answer("Готово")

@dp.message(Command("review"))
async def admin_review(m: Message):
    """Скрытая команда: показать анкеты на проверке по жалобам."""
    if not is_admin(m.from_user.id):
        return
    cur = await db.execute("SELECT * FROM users WHERE status='hidden' ORDER BY uid LIMIT 10")
    rows = await cur.fetchall()
    if not rows:
        return await m.answer("✅ Нет анкет на проверке по жалобам.")
    for u in rows:
        cnt = (await (await db.execute("SELECT COUNT(DISTINCT who) c FROM reports WHERE whom=?", (u["uid"],))).fetchone())["c"]
        ph = photos_of(u)
        cap = (f"🚩 <b>Жалобы</b> (×{cnt})\nID: <code>{u['uid']}</code>\n{LINE}\n" + profile_caption(u))
        if ph:
            await m.answer_photo(ph[0], caption=cap, reply_markup=review_kb(u["uid"]))
        else:
            await m.answer(cap, reply_markup=review_kb(u["uid"]))


# ---- Апелляции (пересмотр блокировки) ----
@dp.callback_query(F.data.startswith("apl_"))
async def appeal_decision(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет прав", show_alert=True)
    _, decision, uid_s = c.data.split("_")
    uid = int(uid_s)
    await db.execute("DELETE FROM appeals WHERE uid=?", (uid,))
    await db.commit()
    u = await get_user(uid)
    if not u:
        return await c.answer("Анкета удалена", show_alert=True)
    if decision == "ok":
        # разблокировать, сбросить нарушения, вернуть в активные
        await db.execute("UPDATE users SET status='active', strikes=0, reject_reason='' WHERE uid=?", (uid,))
        await db.execute("DELETE FROM reports WHERE whom=?", (uid,))
        await db.commit(); invalidate(uid)
        note = "\n\n✅ АПЕЛЛЯЦИЯ ОДОБРЕНА"
        try:
            await bot.send_message(uid, "✅ <b>Пересмотр завершён</b>\n"
                                        "Блокировка снята, анкета снова активна. Извини за неудобства 💞",
                                   reply_markup=main_menu())
        except Exception:
            pass
    else:
        note = "\n\n❌ АПЕЛЛЯЦИЯ ОТКЛОНЕНА"
        try:
            await bot.send_message(uid, "❌ <b>Пересмотр завершён</b>\n"
                                        "Решение оставлено в силе. Блокировка сохраняется.")
        except Exception:
            pass
    try:
        if c.message.photo:
            await c.message.edit_caption(caption=(c.message.caption or "") + note)
        else:
            await c.message.edit_text((c.message.text or "") + note)
    except Exception:
        pass
    await c.answer("Готово")

@dp.message(Command("appeals"))
async def admin_appeals(m: Message):
    """Скрытая команда: показать поданные апелляции."""
    if not is_admin(m.from_user.id):
        return
    cur = await db.execute("SELECT * FROM appeals ORDER BY ts LIMIT 10")
    rows = await cur.fetchall()
    if not rows:
        return await m.answer("✅ Нет заявок на пересмотр.")
    for a in rows:
        u = await get_user(a["uid"])
        ph = photos_of(u) if u else []
        cap = (f"🛟 <b>Апелляция</b>\nID: <code>{a['uid']}</code>\n"
               f"Статус: {u['status'] if u else '?'}\n"
               f"Причина: {esc(u['reject_reason']) if u and u['reject_reason'] else '—'}\n{LINE}\n"
               f"💬 «{esc(a['text'])}»\n{LINE}\n" + (profile_caption(u) if u else ""))
        if ph:
            await m.answer_photo(ph[0], caption=cap, reply_markup=appeal_kb(a["uid"]))
        else:
            await m.answer(cap, reply_markup=appeal_kb(a["uid"]))


# ---- Управление админами (скрытые команды, только для админов) ----
async def resolve_uid(arg: str) -> Optional[int]:
    """ID или @username (если человек писал боту)."""
    arg = arg.strip()
    if arg.isdigit():
        return int(arg)
    if arg.startswith("@"):
        try:
            chat = await bot.get_chat(arg)
            return chat.id
        except Exception:
            return None
    return None

@dp.message(Command("addadmin"))
async def admin_add(m: Message):
    if not is_admin(m.from_user.id):
        return
    parts = (m.text or "").split()
    if len(parts) < 2:
        return await m.answer("Использование: /addadmin &lt;id&gt; или /addadmin @username\n"
                              "<i>По @username работает, только если человек уже писал боту.</i>")
    uid = await resolve_uid(parts[1])
    if uid is None:
        return await m.answer("Не нашёл пользователя. По @username — он должен сначала открыть бота (/start). "
                              "Надёжнее добавлять по числовому ID.")
    if uid in ADMIN_IDS:
        return await m.answer("Этот пользователь уже главный админ.")
    await db.execute("INSERT OR REPLACE INTO admins(uid,added_by,ts) VALUES(?,?,?)", (uid, m.from_user.id, now()))
    await db.commit()
    await load_admins()
    try:
        await bot.send_message(uid, "🛡 Вам выданы права администратора бота. Команды: /admin")
    except Exception:
        pass
    await m.answer(f"✅ Админ добавлен: <code>{uid}</code>")

@dp.message(Command("deladmin"))
async def admin_del(m: Message):
    if not is_admin(m.from_user.id):
        return
    parts = (m.text or "").split()
    if len(parts) < 2:
        return await m.answer("Использование: /deladmin &lt;id&gt; или /deladmin @username")
    uid = await resolve_uid(parts[1])
    if uid is None:
        return await m.answer("Не нашёл пользователя. Попробуй по числовому ID.")
    if uid in ADMIN_IDS:
        return await m.answer("Главного админа удалить нельзя.")
    await db.execute("DELETE FROM admins WHERE uid=?", (uid,))
    await db.commit()
    await load_admins()
    await m.answer(f"✅ Админ удалён: <code>{uid}</code>")

@dp.message(Command("admins"))
async def admin_list(m: Message):
    if not is_admin(m.from_user.id):
        return
    lines = [f"👑 <code>{a}</code> (главный)" for a in ADMIN_IDS]
    for a in sorted(ADMIN_CACHE):
        lines.append(f"🛡 <code>{a}</code>")
    await m.answer("<b>Администраторы:</b>\n" + "\n".join(lines))

@dp.message(Command("admin"))
@dp.message(Command("stats"))
async def admin_stats(m: Message):
    if not is_admin(m.from_user.id):
        return
    async def cnt(where):
        return (await (await db.execute(f"SELECT COUNT(*) c FROM users WHERE {where}")).fetchone())["c"]
    total = await cnt("1=1")
    active = await cnt("status='active'")
    pending = await cnt("status='pending'")
    hidden = await cnt("status='hidden'")
    banned = await cnt("status='banned'")
    intop = await cnt(f"top_until > {now()}")
    matches = (await (await db.execute(
        "SELECT COUNT(*) c FROM likes l1 JOIN likes l2 ON l1.who=l2.whom AND l1.whom=l2.who")).fetchone())["c"] // 2
    pay = await (await db.execute("SELECT COUNT(*) c, COALESCE(SUM(amount),0) s FROM payments")).fetchone()
    cphoto = "NudeNet" if NUDE_OK else ("opennsfw2" if OPENNSFW_OK else "❌ нет")
    cocr = "вкл" if OCR_OK else "выкл"
    await m.answer(
        f"📊 <b>Статистика</b>\n{LINE}\n"
        f"👥 Пользователей: <b>{total}</b>\n"
        f"✅ Активных: {active} · 🕓 Модерация: {pending}\n"
        f"💎 В топе сейчас: {intop}\n"
        f"🚩 На проверке (жалобы): {hidden} · ⛔ Забанено: {banned}\n"
        f"💞 Метчей: {matches}\n"
        f"⭐ Платежей: {pay['c']} на {pay['s']} звёзд\n"
        f"🛡 Цензура фото: {cphoto} · OCR: {cocr}\n{LINE}\n"
        f"<b>Команды:</b>\n"
        f"/review — анкеты на проверке по жалобам\n"
        f"/appeals — заявки на пересмотр (апелляции)\n"
        f"/givetop &lt;id&gt; &lt;дней&gt; — 💎 Супер бесплатно\n"
        f"/givevip &lt;id&gt; &lt;дней&gt; — 👑 VIP (скрытый, выше всех)\n"
        f"/delvip &lt;id&gt; — снять 👑 VIP\n"
        f"/user &lt;id&gt; — инфо о пользователе\n"
        f"/broadcast &lt;текст&gt; — рассылка всем\n"
        f"/send &lt;id&gt; &lt;текст&gt; — личное сообщение одному\n"
        f"/ban &lt;id&gt; · /unban &lt;id&gt; · /refund &lt;charge_id&gt;\n"
        f"/addadmin &lt;id&gt; · /deladmin &lt;id&gt; · /admins")

@dp.message(Command("givetop"))
async def admin_givetop(m: Message):
    if not is_admin(m.from_user.id):
        return
    parts = (m.text or "").split()
    if len(parts) < 3 or not parts[1].isdigit() or not parts[2].isdigit():
        return await m.answer("Использование: /givetop &lt;id&gt; &lt;дней&gt;\nВыдаёт 💎 Супер Премиум бесплатно.")
    uid, days = int(parts[1]), int(parts[2])
    u = await get_user(uid)
    if not u:
        return await m.answer("Пользователь не найден (он должен сначала создать анкету).")
    base = max(now(), u["top_until"] or 0)
    until = base + days * 86400
    await db.execute("UPDATE users SET top_tier=2, top_until=? WHERE uid=?", (until, uid))
    await db.commit(); invalidate(uid)
    try:
        await bot.send_message(uid, f"🎁 <b>Тебе подарили 💎 Супер Премиум!</b>\nДействует до <b>{fmt_dt(until)}</b> 🔥")
    except Exception:
        pass
    await m.answer(f"✅ Выдан 💎 Супер Премиум пользователю <code>{uid}</code> до {fmt_dt(until)}.")

@dp.message(Command("givevip"))
async def admin_givevip(m: Message):
    """СКРЫТО: выдать 👑 VIP — высший уровень, выше всех. Купить нельзя, только так."""
    if not is_admin(m.from_user.id):
        return
    parts = (m.text or "").split()
    if len(parts) < 3 or not parts[1].isdigit() or not parts[2].isdigit():
        return await m.answer("Использование: /givevip &lt;id&gt; &lt;дней&gt;\n"
                              "Выдаёт 👑 VIP (выше всех). Для «навсегда» — 3650 дней.")
    uid, days = int(parts[1]), int(parts[2])
    u = await get_user(uid)
    if not u:
        return await m.answer("Пользователь не найден (он должен сначала создать анкету).")
    until = now() + days * 86400
    await db.execute("UPDATE users SET top_tier=3, top_until=? WHERE uid=?", (until, uid))
    await db.commit(); invalidate(uid)
    try:
        await bot.send_message(uid, f"👑 <b>Тебе выдан VIP-статус!</b>\nДействует до <b>{fmt_dt(until)}</b> ✨")
    except Exception:
        pass
    await m.answer(f"👑 Выдан VIP пользователю <code>{uid}</code> до {fmt_dt(until)}.")

@dp.message(Command("delvip"))
async def admin_delvip(m: Message):
    """СКРЫТО: снять 👑 VIP."""
    if not is_admin(m.from_user.id):
        return
    parts = (m.text or "").split()
    if len(parts) < 2 or not parts[1].isdigit():
        return await m.answer("Использование: /delvip &lt;id&gt;")
    uid = int(parts[1])
    await db.execute("UPDATE users SET top_tier=0, top_until=0 WHERE uid=? AND top_tier=3", (uid,))
    await db.commit(); invalidate(uid)
    await m.answer(f"✅ VIP снят с пользователя <code>{uid}</code>.")

@dp.message(Command("user"))
async def admin_user(m: Message):
    if not is_admin(m.from_user.id):
        return
    parts = (m.text or "").split()
    if len(parts) < 2 or not parts[1].isdigit():
        return await m.answer("Использование: /user &lt;id&gt;")
    uid = int(parts[1])
    u = await get_user(uid)
    if not u:
        return await m.answer("Пользователь не найден.")
    likes_in = (await (await db.execute("SELECT COUNT(*) c FROM likes WHERE whom=?", (uid,))).fetchone())["c"]
    reps = (await (await db.execute("SELECT COUNT(DISTINCT who) c FROM reports WHERE whom=?", (uid,))).fetchone())["c"]
    top = "нет"
    if top_active(u):
        if u["top_tier"] == 3:
            top = "👑 VIP"
        elif u["top_tier"] == 2:
            top = "💎 Супер"
        else:
            top = "⭐ Премиум"
        top += f" до {fmt_dt(u['top_until'])}"
    await m.answer(
        f"👤 <b>{esc(u['name'])}</b>, {u['age']} · <code>{uid}</code>\n{LINE}\n"
        f"Статус: {u['status']}\n"
        f"⚠️ Нарушений: {u['strikes']}/{MAX_STRIKES}\n"
        f"Топ: {top}\n"
        f"❤️ Входящих лайков: {likes_in}\n"
        f"🚩 Жалоб (уникальных): {reps}")

@dp.message(Command("broadcast"))
async def admin_broadcast(m: Message):
    if not is_admin(m.from_user.id):
        return
    text = (m.text or "")[len("/broadcast"):].strip()
    if not text:
        return await m.answer("Использование: /broadcast &lt;текст рассылки&gt;\n\n"
                              "💡 Для одного человека: /send &lt;id&gt; &lt;текст&gt;")
    cur = await db.execute("SELECT COUNT(*) c FROM users WHERE status NOT IN ('banned')")
    n = (await cur.fetchone())["c"]
    # сохраняем текст и просим подтверждение (защита от случайной рассылки)
    BROADCAST_PENDING[m.from_user.id] = text
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text=f"✅ Разослать {n} людям", callback_data="bc_yes"),
        InlineKeyboardButton(text="❌ Отмена", callback_data="bc_no"),
    ]])
    await m.answer(f"📣 <b>Подтверди рассылку</b>\n{LINE}\n{text}\n{LINE}\n"
                   f"Получателей: <b>{n}</b>. Отправить?", reply_markup=kb)

@dp.callback_query(F.data == "bc_no")
async def broadcast_cancel(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет прав", show_alert=True)
    BROADCAST_PENDING.pop(c.from_user.id, None)
    await c.message.edit_text("❌ Рассылка отменена.")
    await c.answer()

@dp.callback_query(F.data == "bc_yes")
async def broadcast_confirm(c: CallbackQuery):
    if not is_admin(c.from_user.id):
        return await c.answer("Нет прав", show_alert=True)
    text = BROADCAST_PENDING.pop(c.from_user.id, None)
    if not text:
        return await c.answer("Текст рассылки не найден, начни заново через /broadcast", show_alert=True)
    await c.message.edit_text("📣 Рассылка запущена…")
    cur = await db.execute("SELECT uid FROM users WHERE status NOT IN ('banned')")
    rows = await cur.fetchall()
    ok = fail = 0
    for r in rows:
        try:
            await bot.send_message(r["uid"], f"📣 <b>Объявление</b>\n{LINE}\n{text}")
            ok += 1
        except Exception:
            fail += 1
        await asyncio.sleep(0.05)
    await c.message.answer(f"✅ Готово. Доставлено: {ok}, не дошло: {fail}.")
    await c.answer()

@dp.message(Command("send"))
async def admin_send(m: Message):
    """Личное сообщение одному пользователю по ID."""
    if not is_admin(m.from_user.id):
        return
    parts = (m.text or "").split(maxsplit=2)
    if len(parts) < 3 or not parts[1].isdigit():
        return await m.answer("Использование: /send &lt;id&gt; &lt;текст&gt;\n"
                              "Пример: /send 123456789 Привет! Это сообщение от администрации.")
    uid = int(parts[1])
    text = parts[2]
    target = await get_user(uid)
    if not target:
        return await m.answer(f"Пользователь <code>{uid}</code> не найден.")
    try:
        await bot.send_message(uid, f"✉️ <b>Сообщение от администрации</b>\n{LINE}\n{text}")
        await m.answer(f"✅ Отправлено пользователю <b>{esc(target['name'])}</b> (<code>{uid}</code>).")
    except Exception as e:
        await m.answer(f"❌ Не удалось отправить: {e}\n(Возможно, пользователь заблокировал бота.)")

@dp.message(Command("ban"))
async def admin_ban(m: Message):
    if not is_admin(m.from_user.id):
        return
    parts = (m.text or "").split()
    if len(parts) < 2 or not parts[1].isdigit():
        return await m.answer("Использование: /ban &lt;user_id&gt;")
    uid = int(parts[1])
    await db.execute("UPDATE users SET status='banned' WHERE uid=?", (uid,))
    await db.commit(); invalidate(uid)
    try:
        await bot.send_message(uid, "⛔ Ваша анкета заблокирована администрацией.", reply_markup=unban_kb())
    except Exception:
        pass
    await m.answer(f"⛔ Пользователь {uid} забанен.")

@dp.message(Command("unban"))
async def admin_unban(m: Message):
    if not is_admin(m.from_user.id):
        return
    parts = (m.text or "").split()
    if len(parts) < 2 or not parts[1].isdigit():
        return await m.answer("Использование: /unban &lt;user_id&gt;")
    uid = int(parts[1])
    await db.execute("DELETE FROM reports WHERE whom=?", (uid,))
    await db.execute("UPDATE users SET status='active', strikes=0 WHERE uid=?", (uid,))
    await db.commit(); invalidate(uid)
    try:
        await bot.send_message(uid, "✅ Блокировка снята администрацией. Анкета снова активна.")
    except Exception:
        pass
    await m.answer(f"✅ Пользователь {uid} разбанен (статус active, нарушения и жалобы сброшены).")

@dp.message(Command("refund"))
async def admin_refund(m: Message):
    if not is_admin(m.from_user.id):
        return
    parts = (m.text or "").split()
    if len(parts) < 2:
        return await m.answer("Использование: /refund &lt;charge_id&gt;")
    charge = parts[1]
    row = await (await db.execute("SELECT uid FROM payments WHERE charge_id=?", (charge,))).fetchone()
    if not row:
        return await m.answer("Платёж не найден.")
    try:
        await bot.refund_star_payment(row["uid"], charge)
        await m.answer("✅ Возврат выполнен.")
        try:
            await bot.send_message(row["uid"], "↩️ Вам возвращены звёзды за покупку.")
        except Exception:
            pass
    except Exception as e:
        await m.answer(f"Ошибка возврата: {e}")


# ==================== RUN ====================
async def main():
    global NUDE_DETECTOR, BOT_USERNAME
    await init_db()
    await load_admins()
    try:
        _me = await bot.get_me()
        BOT_USERNAME = _me.username or ""
        logging.info(f"Bot username: @{BOT_USERNAME}")
    except Exception:
        pass
    try:
        await bot.set_my_commands([
            BotCommand(command="start", description="Меню / создать анкету"),
            BotCommand(command="edit", description="Изменить анкету"),
            BotCommand(command="paysupport", description="Поддержка по оплате"),
        ])
    except Exception:
        pass
    if NUDE_OK:
        NUDE_DETECTOR = await asyncio.to_thread(NudeDetector)
        logging.info("Цензура фото: NudeNet")
    elif OPENNSFW_OK:
        asyncio.get_running_loop().run_in_executor(None, lambda: _n2.make_open_nsfw_model())
        logging.info("Цензура фото: opennsfw2")
    else:
        logging.info("Цензура фото: ручная модерация (моделей нет)")
    logging.info(f"OCR текста на фото: {'включён' if OCR_OK else 'выключен'}")
    logging.info("Bot started")
    await dp.start_polling(bot)

if __name__ == "__main__":
    asyncio.run(main())
