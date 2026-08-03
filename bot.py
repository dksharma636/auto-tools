#!/usr/bin/env python3
"""
Telegram Account + Channel Management Bot
Production-ready single-file system using legitimate Telethon + aiogram APIs only.
Run: python bot.py
Requires: BOT_TOKEN environment variable
"""

from __future__ import annotations

import asyncio
import html
import json
import logging
import os
import re
import secrets
import shutil
import time
import traceback
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from enum import Enum
from pathlib import Path
from typing import Any, Awaitable, Callable, Dict, List, Optional, Set, Tuple

from aiogram import Bot, Dispatcher, F, Router
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramBadRequest, TelegramRetryAfter
from aiogram.filters import Command, CommandStart, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
)
from telethon import TelegramClient, errors, functions, types as tl_types
from telethon.sessions import StringSession
from telethon.tl.custom.dialog import Dialog
from telethon.tl.types import (
    Channel,
    ChannelParticipantAdmin,
    ChannelParticipantCreator,
    ChannelParticipantsAdmins,
    ChannelParticipantsBots,
    ChannelParticipantsRecent,
    ChannelParticipantsSearch,
    ChatAdminRights,
    InputPeerChannel,
    User,
)

# ---------------------------------------------------------------------------
# Configuration & paths
# ---------------------------------------------------------------------------

BASE_DIR = Path(__file__).resolve().parent
DATA_DIR = BASE_DIR / "data"
SESSIONS_DIR = DATA_DIR / "sessions"
USERS_DIR = DATA_DIR / "users"
LOGS_DIR = DATA_DIR / "logs"

for _d in (DATA_DIR, SESSIONS_DIR, USERS_DIR, LOGS_DIR):
    _d.mkdir(parents=True, exist_ok=True)

BOT_TOKEN = os.environ.get("BOT_TOKEN", "").strip()
if not BOT_TOKEN:
    raise SystemExit(
        "ERROR: BOT_TOKEN environment variable is required.\n"
        "Export it first, e.g.: export BOT_TOKEN='123456:ABC-DEF'\n"
        "Then run: python bot.py"
    )

# Soft limits (legitimate API usage only)
MAX_CONCURRENT_WORKERS = 6
DEFAULT_WORKERS = 3
BULK_QUEUE_SIZE = 500
PROGRESS_EDIT_INTERVAL = 1.5
MEMBER_PAGE_SIZE = 10
CHANNEL_PAGE_SIZE = 8
ACTIVITY_LOG_MAX = 200
SESSION_STRING_NAME = "session.string"
USER_CFG_NAME = "config.json"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)-7s | %(name)s | %(message)s",
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler(LOGS_DIR / "bot.log", encoding="utf-8"),
    ],
)
log = logging.getLogger("tg_manager")

# Never log sensitive auth material
class _RedactFilter(logging.Filter):
    _PAT = re.compile(
        r"(otp|code|password|api[_ ]?hash|session|2fa|two.?step)",
        re.I,
    )

    def filter(self, record: logging.LogRecord) -> bool:
        msg = record.getMessage()
        if self._PAT.search(msg) and any(
            k in msg.lower()
            for k in ("enter", "received", "value=", "got code", "password=")
        ):
            record.msg = "[REDACTED sensitive auth log line]"
            record.args = ()
        return True


for h in logging.root.handlers:
    h.addFilter(_RedactFilter())


# ---------------------------------------------------------------------------
# FSM
# ---------------------------------------------------------------------------


class LoginFSM(StatesGroup):
    api_id = State()
    api_hash = State()
    phone = State()
    otp = State()
    password = State()


class SearchFSM(StatesGroup):
    query = State()
    by_id = State()
    by_username = State()


class SettingsFSM(StatesGroup):
    log_channel = State()
    workers = State()


class BulkFSM(StatesGroup):
    confirm = State()
    input_ids = State()


class MemberFSM(StatesGroup):
    confirm_remove = State()


# ---------------------------------------------------------------------------
# User store (isolated per Telegram user id)
# ---------------------------------------------------------------------------


def user_dir(uid: int) -> Path:
    p = USERS_DIR / str(uid)
    p.mkdir(parents=True, exist_ok=True)
    return p


def session_path(uid: int) -> Path:
    return SESSIONS_DIR / f"{uid}.session"


def session_string_path(uid: int) -> Path:
    return SESSIONS_DIR / f"{uid}.string"


def load_user_cfg(uid: int) -> Dict[str, Any]:
    path = user_dir(uid) / USER_CFG_NAME
    if not path.exists():
        return {
            "log_channel_id": None,
            "workers": DEFAULT_WORKERS,
            "selected_channel_id": None,
            "phone_hint": None,
            "connected_at": None,
            "activity": [],
        }
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        data.setdefault("activity", [])
        data.setdefault("workers", DEFAULT_WORKERS)
        return data
    except Exception:
        return {
            "log_channel_id": None,
            "workers": DEFAULT_WORKERS,
            "selected_channel_id": None,
            "phone_hint": None,
            "connected_at": None,
            "activity": [],
        }


def save_user_cfg(uid: int, cfg: Dict[str, Any]) -> None:
    path = user_dir(uid) / USER_CFG_NAME
    # Never persist secrets
    safe = {k: v for k, v in cfg.items() if k not in ("api_hash", "otp", "password", "session")}
    with open(path, "w", encoding="utf-8") as f:
        json.dump(safe, f, ensure_ascii=False, indent=2)


def append_activity(uid: int, event: str) -> None:
    cfg = load_user_cfg(uid)
    act = cfg.get("activity") or []
    act.append({"ts": datetime.now(timezone.utc).isoformat(), "event": event})
    cfg["activity"] = act[-ACTIVITY_LOG_MAX:]
    save_user_cfg(uid, cfg)


def mask_phone(phone: Optional[str]) -> str:
    if not phone:
        return "Hidden"
    digits = re.sub(r"\D", "", phone)
    if len(digits) < 6:
        return "Hidden"
    return f"+{digits[:2]}•••{digits[-2:]}"


# ---------------------------------------------------------------------------
# Session / client manager (isolated per owner)
# ---------------------------------------------------------------------------


class ClientManager:
    """Owns authenticated Telethon clients; one per bot user, isolated."""

    def __init__(self) -> None:
        self._clients: Dict[int, TelegramClient] = {}
        self._locks: Dict[int, asyncio.Lock] = defaultdict(asyncio.Lock)
        self._phone_code_hashes: Dict[int, str] = {}
        self._temp_creds: Dict[int, Dict[str, Any]] = {}

    def lock(self, uid: int) -> asyncio.Lock:
        return self._locks[uid]

    def set_temp_creds(self, uid: int, **kwargs: Any) -> None:
        self._temp_creds.setdefault(uid, {}).update(kwargs)

    def get_temp_creds(self, uid: int) -> Dict[str, Any]:
        return self._temp_creds.get(uid, {})

    def clear_temp_creds(self, uid: int) -> None:
        self._temp_creds.pop(uid, None)
        self._phone_code_hashes.pop(uid, None)

    def get_client(self, uid: int) -> Optional[TelegramClient]:
        return self._clients.get(uid)

    async def disconnect(self, uid: int) -> None:
        async with self.lock(uid):
            client = self._clients.pop(uid, None)
            if client:
                try:
                    if client.is_connected():
                        await client.disconnect()
                except Exception as e:
                    log.warning("disconnect uid=%s: %s", uid, type(e).__name__)
            self.clear_temp_creds(uid)

    async def logout_and_wipe(self, uid: int) -> None:
        async with self.lock(uid):
            client = self._clients.pop(uid, None)
            if client:
                try:
                    if client.is_connected():
                        try:
                            await client.log_out()
                        except Exception:
                            pass
                        try:
                            await client.disconnect()
                        except Exception:
                            pass
                except Exception:
                    pass
            self.clear_temp_creds(uid)
            for p in (session_path(uid), session_string_path(uid)):
                try:
                    if p.exists():
                        p.unlink()
                except Exception:
                    pass
            # wipe journal files
            for p in SESSIONS_DIR.glob(f"{uid}.session*"):
                try:
                    p.unlink()
                except Exception:
                    pass

    async def is_authorized(self, uid: int) -> bool:
        client = await self.ensure_client(uid)
        if not client:
            return False
        try:
            return await client.is_user_authorized()
        except Exception:
            return False

    async def ensure_client(self, uid: int) -> Optional[TelegramClient]:
        """Load existing session if present."""
        async with self.lock(uid):
            if uid in self._clients:
                c = self._clients[uid]
                if not c.is_connected():
                    try:
                        await c.connect()
                    except Exception:
                        self._clients.pop(uid, None)
                        return None
                return c

            sp = session_string_path(uid)
            fp = session_path(uid)
            cfg = load_user_cfg(uid)
            api_id = cfg.get("api_id")
            api_hash = cfg.get("_api_hash_enc")  # stored only if user opts; we use file

            # Prefer string session + credentials file
            cred_path = user_dir(uid) / "api.json"
            if not cred_path.exists():
                return None
            try:
                with open(cred_path, "r", encoding="utf-8") as f:
                    creds = json.load(f)
                api_id = int(creds["api_id"])
                api_hash = str(creds["api_hash"])
            except Exception:
                return None

            session: Any
            if sp.exists():
                try:
                    raw = sp.read_text(encoding="utf-8").strip()
                    session = StringSession(raw)
                except Exception:
                    session = str(fp)
            else:
                session = str(fp)

            client = TelegramClient(
                session,
                api_id,
                api_hash,
                device_model="TG-Manager",
                system_version="1.0",
                app_version="1.0.0",
                lang_code="en",
                system_lang_code="en",
            )
            try:
                await client.connect()
                if not await client.is_user_authorized():
                    await client.disconnect()
                    return None
                # persist string session
                try:
                    s = StringSession.save(client.session)  # type: ignore
                    sp.write_text(s, encoding="utf-8")
                    try:
                        os.chmod(sp, 0o600)
                    except Exception:
                        pass
                except Exception:
                    pass
                self._clients[uid] = client
                return client
            except Exception as e:
                log.warning("ensure_client uid=%s failed: %s", uid, type(e).__name__)
                try:
                    await client.disconnect()
                except Exception:
                    pass
                return None

    async def begin_login(self, uid: int, api_id: int, api_hash: str) -> TelegramClient:
        async with self.lock(uid):
            old = self._clients.pop(uid, None)
            if old:
                try:
                    await old.disconnect()
                except Exception:
                    pass
            # fresh file session during login
            for p in SESSIONS_DIR.glob(f"{uid}.session*"):
                try:
                    p.unlink()
                except Exception:
                    pass
            client = TelegramClient(
                str(session_path(uid)),
                api_id,
                api_hash,
                device_model="TG-Manager",
                system_version="1.0",
                app_version="1.0.0",
            )
            await client.connect()
            self._clients[uid] = client
            self.set_temp_creds(uid, api_id=api_id, api_hash=api_hash)
            return client

    async def send_code(self, uid: int, phone: str) -> None:
        client = self._clients.get(uid)
        if not client:
            raise RuntimeError("Client not initialized")
        result = await client.send_code_request(phone)
        self._phone_code_hashes[uid] = result.phone_code_hash
        self.set_temp_creds(uid, phone=phone)

    async def sign_in_code(self, uid: int, code: str) -> str:
        """Returns 'ok' | '2fa' | error message key."""
        client = self._clients.get(uid)
        if not client:
            return "no_client"
        phone = self.get_temp_creds(uid).get("phone")
        phone_code_hash = self._phone_code_hashes.get(uid)
        if not phone or not phone_code_hash:
            return "no_hash"
        try:
            await client.sign_in(phone=phone, code=code, phone_code_hash=phone_code_hash)
            await self._finalize_auth(uid, client)
            return "ok"
        except errors.SessionPasswordNeededError:
            return "2fa"
        except errors.PhoneCodeInvalidError:
            return "invalid_otp"
        except errors.PhoneCodeExpiredError:
            return "expired_otp"
        except errors.FloodWaitError as e:
            return f"flood:{e.seconds}"
        except Exception as e:
            log.warning("sign_in_code uid=%s: %s", uid, type(e).__name__)
            return "error"

    async def sign_in_password(self, uid: int, password: str) -> str:
        client = self._clients.get(uid)
        if not client:
            return "no_client"
        try:
            await client.sign_in(password=password)
            await self._finalize_auth(uid, client)
            return "ok"
        except errors.PasswordHashInvalidError:
            return "invalid_2fa"
        except errors.FloodWaitError as e:
            return f"flood:{e.seconds}"
        except Exception as e:
            log.warning("sign_in_password uid=%s: %s", uid, type(e).__name__)
            return "error"

    async def _finalize_auth(self, uid: int, client: TelegramClient) -> None:
        creds = self.get_temp_creds(uid)
        api_id = creds.get("api_id")
        api_hash = creds.get("api_hash")
        phone = creds.get("phone")
        if api_id and api_hash:
            cred_path = user_dir(uid) / "api.json"
            with open(cred_path, "w", encoding="utf-8") as f:
                json.dump({"api_id": int(api_id), "api_hash": str(api_hash)}, f)
            try:
                os.chmod(cred_path, 0o600)
            except Exception:
                pass
        try:
            s = StringSession.save(client.session)  # type: ignore
            session_string_path(uid).write_text(s, encoding="utf-8")
            try:
                os.chmod(session_string_path(uid), 0o600)
            except Exception:
                pass
        except Exception:
            pass
        cfg = load_user_cfg(uid)
        cfg["api_id"] = int(api_id) if api_id else cfg.get("api_id")
        cfg["phone_hint"] = mask_phone(phone) if phone else cfg.get("phone_hint")
        cfg["connected_at"] = datetime.now(timezone.utc).isoformat()
        save_user_cfg(uid, cfg)
        # Wipe secrets from memory
        self.clear_temp_creds(uid)
        append_activity(uid, "Account connected")


CM = ClientManager()


# ---------------------------------------------------------------------------
# Admin log channel (never secrets)
# ---------------------------------------------------------------------------


async def admin_log(bot: Bot, uid: int, text: str) -> None:
    cfg = load_user_cfg(uid)
    ch = cfg.get("log_channel_id")
    if not ch:
        return
    # Safety: strip anything that looks like secrets
    safe = text
    for pat in (
        r"\b\d{5,6}\b",  # possible OTP-looking
    ):
        pass  # do not strip numbers blindly from operational logs
    try:
        await bot.send_message(
            int(ch),
            f"📋 <b>Log</b> · user <code>{uid}</code>\n{safe}",
            parse_mode=ParseMode.HTML,
            disable_web_page_preview=True,
        )
    except Exception as e:
        log.debug("admin_log fail uid=%s: %s", uid, type(e).__name__)


# ---------------------------------------------------------------------------
# UI helpers
# ---------------------------------------------------------------------------


def kb(rows: List[List[Tuple[str, str]]]) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text=t, callback_data=c) for t, c in row]
            for row in rows
        ]
    )


def progress_bar(pct: float, width: int = 10) -> str:
    pct = max(0.0, min(100.0, pct))
    filled = int(round(width * pct / 100.0))
    return "█" * filled + "░" * (width - filled)


WELCOME_TEXT = (
    "<b>✦ TELEGRAM MANAGER ✦</b>\n\n"
    "🔐 <b>Secure Account Connection</b>\n"
    "📡 Connect your Telegram account to continue.\n\n"
    "<i>Uses official Telegram API (Telethon). "
    "OTP and 2FA are never logged or shared.</i>"
)

DASHBOARD_TMPL = (
    "╭━━━〔 ✦ TELEGRAM MANAGER ✦ 〕━━━╮\n"
    "┃ 👤 Account: <b>{status}</b>\n"
    "┃ 📱 Phone: <code>{phone}</code>\n"
    "┃ 🟢 Status: <b>{online}</b>\n"
    "┃ 📡 Channel: <code>{channel}</code>\n"
    "╰━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━╯\n\n"
    "Select a module:"
)


def dashboard_kb() -> InlineKeyboardMarkup:
    return kb(
        [
            [("📡 CHANNELS", "nav:channels"), ("👥 MEMBERS", "nav:members")],
            [("🔎 SEARCH MEMBER", "nav:search"), ("🗑 MEMBER MGMT", "nav:mmgmt")],
            [("⚡ BULK ACTION", "nav:bulk"), ("📊 STATISTICS", "nav:stats")],
            [("📝 ACTIVITY LOGS", "nav:activity"), ("⚙️ SETTINGS", "nav:settings")],
            [("🔐 ACCOUNT", "nav:account"), ("🚪 LOGOUT", "nav:logout")],
        ]
    )


def back_dash_kb(extra: Optional[List[List[Tuple[str, str]]]] = None) -> InlineKeyboardMarkup:
    rows = list(extra or [])
    rows.append([("« Dashboard", "nav:dashboard")])
    return kb(rows)


def cancel_kb(cb: str = "nav:cancel") -> InlineKeyboardMarkup:
    return kb([[("❌ Cancel", cb)]])


# ---------------------------------------------------------------------------
# Bulk engine
# ---------------------------------------------------------------------------


@dataclass
class BulkStats:
    total: int = 0
    processed: int = 0
    success: int = 0
    failed: int = 0
    flood_waits: int = 0
    started_at: float = field(default_factory=time.monotonic)
    stopped: bool = False
    finished: bool = False
    last_error: str = ""

    @property
    def speed(self) -> float:
        elapsed = max(0.001, time.monotonic() - self.started_at)
        return self.processed / elapsed

    @property
    def pct(self) -> float:
        if self.total <= 0:
            return 0.0
        return 100.0 * self.processed / self.total


@dataclass
class BulkJob:
    uid: int
    name: str
    items: List[Any]
    worker_fn: Callable[[TelegramClient, Any, "BulkJob"], Awaitable[bool]]
    workers: int = DEFAULT_WORKERS
    cancel_event: asyncio.Event = field(default_factory=asyncio.Event)
    stats: BulkStats = field(default_factory=BulkStats)
    progress_msg_id: Optional[int] = None
    progress_chat_id: Optional[int] = None
    _task: Optional[asyncio.Task] = None


class BulkEngine:
    def __init__(self) -> None:
        self._jobs: Dict[int, BulkJob] = {}
        self._lock = asyncio.Lock()

    def get(self, uid: int) -> Optional[BulkJob]:
        return self._jobs.get(uid)

    async def stop(self, uid: int) -> Optional[BulkJob]:
        job = self._jobs.get(uid)
        if not job:
            return None
        job.cancel_event.set()
        job.stats.stopped = True
        return job

    async def run(
        self,
        bot: Bot,
        job: BulkJob,
        chat_id: int,
        message_id: int,
    ) -> BulkStats:
        async with self._lock:
            old = self._jobs.get(job.uid)
            if old and not old.stats.finished:
                old.cancel_event.set()
            self._jobs[job.uid] = job

        job.progress_chat_id = chat_id
        job.progress_msg_id = message_id
        job.stats.total = len(job.items)
        job.stats.started_at = time.monotonic()

        client = await CM.ensure_client(job.uid)
        if not client:
            job.stats.finished = True
            job.stats.last_error = "Not connected"
            return job.stats

        queue: asyncio.Queue = asyncio.Queue(maxsize=BULK_QUEUE_SIZE)
        workers_n = max(1, min(MAX_CONCURRENT_WORKERS, job.workers))

        async def producer() -> None:
            for item in job.items:
                if job.cancel_event.is_set():
                    break
                await queue.put(item)
            for _ in range(workers_n):
                await queue.put(None)  # type: ignore

        async def worker() -> None:
            while not job.cancel_event.is_set():
                item = await queue.get()
                try:
                    if item is None:
                        return
                    # Adaptive small delay
                    await asyncio.sleep(0.05)
                    ok = False
                    try:
                        ok = await job.worker_fn(client, item, job)
                    except errors.FloodWaitError as e:
                        job.stats.flood_waits += 1
                        wait = int(e.seconds) + 1
                        job.stats.last_error = f"FloodWait {wait}s"
                        # Respect Telegram wait; reduce pressure
                        await asyncio.sleep(min(wait, 120))
                        try:
                            ok = await job.worker_fn(client, item, job)
                        except errors.FloodWaitError as e2:
                            job.stats.flood_waits += 1
                            await asyncio.sleep(min(int(e2.seconds) + 1, 180))
                            ok = False
                        except Exception:
                            ok = False
                    except (
                        errors.UserNotParticipantError,
                        errors.UserIdInvalidError,
                        errors.UsernameNotOccupiedError,
                        errors.ChatAdminRequiredError,
                        errors.RightForbiddenError,
                        errors.UserAdminInvalidError,
                        errors.InputUserDeactivatedError,
                        errors.PeerIdInvalidError,
                    ):
                        ok = False
                        job.stats.last_error = "permission/not_found"
                    except errors.RPCError as e:
                        ok = False
                        job.stats.last_error = type(e).__name__
                    except Exception as e:
                        ok = False
                        job.stats.last_error = type(e).__name__

                    job.stats.processed += 1
                    if ok:
                        job.stats.success += 1
                    else:
                        job.stats.failed += 1
                finally:
                    queue.task_done()

        async def progress_loop() -> None:
            last = 0.0
            while not job.stats.finished:
                now = time.monotonic()
                if now - last >= PROGRESS_EDIT_INTERVAL:
                    last = now
                    await self._edit_progress(bot, job)
                if job.cancel_event.is_set() and queue.empty():
                    break
                await asyncio.sleep(0.4)

        prod_t = asyncio.create_task(producer())
        prog_t = asyncio.create_task(progress_loop())
        worker_tasks = [asyncio.create_task(worker()) for _ in range(workers_n)]

        await prod_t
        await asyncio.gather(*worker_tasks, return_exceptions=True)
        job.stats.finished = True
        prog_t.cancel()
        try:
            await prog_t
        except asyncio.CancelledError:
            pass
        await self._edit_progress(bot, job, final=True)
        async with self._lock:
            if self._jobs.get(job.uid) is job:
                # keep briefly for STOP report; mark finished
                pass
        return job.stats

    async def _edit_progress(self, bot: Bot, job: BulkJob, final: bool = False) -> None:
        if not job.progress_chat_id or not job.progress_msg_id:
            return
        s = job.stats
        title = "⛔ OPERATION STOPPED" if s.stopped and final else (
            "✅ OPERATION COMPLETE" if final else "⚡ OPERATION RUNNING"
        )
        text = (
            f"╭━━〔 {title} 〕━━╮\n"
            f"┃ Progress: {progress_bar(s.pct)} {s.pct:.0f}%\n"
            f"┃ Processed: <b>{s.processed}</b> / {s.total}\n"
            f"┃ Success: <b>{s.success}</b>\n"
            f"┃ Failed: <b>{s.failed}</b>\n"
            f"┃ Speed: <b>{s.speed:.1f}</b>/sec\n"
            f"┃ Workers: <b>{job.workers}</b>\n"
            f"┃ FloodWait: <b>{s.flood_waits}</b>\n"
            f"╰━━━━━━━━━━━━━━━━━━━━━━━━━━╯"
        )
        if s.last_error and not final:
            text += f"\n<i>Last: {html.escape(s.last_error)}</i>"
        markup = None
        if not final and not s.stopped:
            markup = kb([[("⛔ STOP NOW", "bulk:stop")]])
        elif final:
            markup = back_dash_kb()
        try:
            await bot.edit_message_text(
                text,
                chat_id=job.progress_chat_id,
                message_id=job.progress_msg_id,
                parse_mode=ParseMode.HTML,
                reply_markup=markup,
            )
        except TelegramRetryAfter as e:
            await asyncio.sleep(e.retry_after)
        except TelegramBadRequest:
            pass
        except Exception:
            pass


BULK = BulkEngine()


# ---------------------------------------------------------------------------
# Telethon helpers
# ---------------------------------------------------------------------------


async def list_admin_channels(client: TelegramClient) -> List[Dict[str, Any]]:
    result: List[Dict[str, Any]] = []
    async for dialog in client.iter_dialogs():
        entity = dialog.entity
        if not isinstance(entity, Channel):
            continue
        # channels & megagroups where we have admin-ish rights
        if not (entity.broadcast or entity.megagroup):
            continue
        admin = bool(getattr(entity, "admin_rights", None) or entity.creator)
        if not admin:
            # try get permissions
            try:
                perms = await client.get_permissions(entity, "me")
                admin = bool(perms.is_admin or perms.is_creator)
            except Exception:
                admin = False
        if not admin:
            continue
        rights = entity.admin_rights
        rights_list = []
        if entity.creator:
            rights_list.append("creator")
        if rights:
            for attr in (
                "ban_users",
                "delete_messages",
                "invite_users",
                "pin_messages",
                "add_admins",
                "manage_call",
                "other",
            ):
                if getattr(rights, attr, False):
                    rights_list.append(attr)
        result.append(
            {
                "id": entity.id,
                "access_hash": entity.access_hash,
                "title": dialog.name or entity.title or str(entity.id),
                "username": entity.username,
                "broadcast": bool(entity.broadcast),
                "megagroup": bool(entity.megagroup),
                "creator": bool(entity.creator),
                "rights": rights_list,
            }
        )
    result.sort(key=lambda x: x["title"].lower())
    return result


async def resolve_channel(client: TelegramClient, channel_id: int) -> Any:
    return await client.get_entity(channel_id)


async def get_member_count(client: TelegramClient, channel: Any) -> int:
    try:
        full = await client(
            functions.channels.GetFullChannelRequest(channel=channel)
        )
        return int(full.full_chat.participants_count or 0)
    except Exception:
        try:
            return int(getattr(channel, "participants_count", 0) or 0)
        except Exception:
            return 0


async def iter_members_page(
    client: TelegramClient,
    channel: Any,
    offset: int,
    limit: int,
    search: str = "",
) -> Tuple[List[Dict[str, Any]], bool]:
    members: List[Dict[str, Any]] = []
    try:
        if search:
            filt = ChannelParticipantsSearch(search)
        else:
            filt = ChannelParticipantsRecent()
        participants = await client.get_participants(
            channel, limit=limit, offset=offset, filter=filt
        )
        for p in participants:
            if not isinstance(p, User):
                continue
            members.append(_user_dict(p))
        has_more = len(participants) >= limit
        return members, has_more
    except errors.FloodWaitError as e:
        await asyncio.sleep(min(int(e.seconds) + 1, 60))
        return [], False
    except Exception as e:
        log.debug("iter_members: %s", type(e).__name__)
        return [], False


def _user_dict(u: User) -> Dict[str, Any]:
    name = " ".join(x for x in (u.first_name, u.last_name) if x) or "Unknown"
    return {
        "id": u.id,
        "username": u.username,
        "name": name,
        "bot": bool(u.bot),
        "scam": bool(getattr(u, "scam", False)),
        "fake": bool(getattr(u, "fake", False)),
        "premium": bool(getattr(u, "premium", False)),
        "restricted": bool(getattr(u, "restricted", False)),
    }


async def find_user(
    client: TelegramClient, channel: Any, query: str
) -> Optional[Dict[str, Any]]:
    query = query.strip()
    if not query:
        return None
    # by id
    if re.fullmatch(r"-?\d+", query):
        try:
            ent = await client.get_entity(int(query))
            if isinstance(ent, User):
                return _user_dict(ent)
        except Exception:
            pass
    # username
    uname = query.lstrip("@")
    try:
        ent = await client.get_entity(uname)
        if isinstance(ent, User):
            return _user_dict(ent)
    except Exception:
        pass
    # search participants
    try:
        parts = await client.get_participants(
            channel, limit=20, filter=ChannelParticipantsSearch(query)
        )
        for p in parts:
            if isinstance(p, User):
                return _user_dict(p)
    except Exception:
        pass
    return None


async def remove_member(client: TelegramClient, channel: Any, user_id: int) -> bool:
    try:
        await client.edit_permissions(
            channel,
            user_id,
            view_messages=False,
        )
        return True
    except errors.UserNotParticipantError:
        return False
    except errors.FloodWaitError:
        raise
    except Exception:
        try:
            await client.kick_participant(channel, user_id)
            return True
        except errors.FloodWaitError:
            raise
        except Exception:
            return False


async def unban_member(client: TelegramClient, channel: Any, user_id: int) -> bool:
    try:
        await client.edit_permissions(channel, user_id, view_messages=True)
        return True
    except errors.FloodWaitError:
        raise
    except Exception:
        return False


# ---------------------------------------------------------------------------
# Bot app
# ---------------------------------------------------------------------------

router = Router()


async def require_auth(uid: int, target: Message | CallbackQuery) -> Optional[TelegramClient]:
    client = await CM.ensure_client(uid)
    if client and await client.is_user_authorized():
        return client
    text = "🔐 Account not connected.\nPress the button to connect."
    markup = kb([[("🔐 CONNECT ACCOUNT", "auth:connect")]])
    if isinstance(target, CallbackQuery):
        await target.message.edit_text(text, reply_markup=markup)  # type: ignore
        await target.answer()
    else:
        await target.answer(text, reply_markup=markup)
    return None


async def require_channel(uid: int, target: Message | CallbackQuery) -> Optional[int]:
    cfg = load_user_cfg(uid)
    cid = cfg.get("selected_channel_id")
    if cid:
        return int(cid)
    text = "📡 No channel selected.\nOpen CHANNELS to choose one."
    markup = kb(
        [
            [("📡 CHANNELS", "nav:channels")],
            [("« Dashboard", "nav:dashboard")],
        ]
    )
    if isinstance(target, CallbackQuery):
        await target.message.edit_text(text, reply_markup=markup)  # type: ignore
        await target.answer()
    else:
        await target.answer(text, reply_markup=markup)
    return None


async def show_dashboard(bot: Bot, chat_id: int, uid: int, message_id: Optional[int] = None) -> None:
    authorized = await CM.is_authorized(uid)
    cfg = load_user_cfg(uid)
    ch = cfg.get("selected_channel_id")
    ch_label = str(ch) if ch else "None"
    text = DASHBOARD_TMPL.format(
        status="Connected" if authorized else "Not connected",
        phone=cfg.get("phone_hint") or "Hidden",
        online="Online" if authorized else "Offline",
        channel=ch_label,
    )
    if not authorized:
        markup = kb([[("🔐 CONNECT ACCOUNT", "auth:connect")]])
    else:
        markup = dashboard_kb()
    try:
        if message_id:
            await bot.edit_message_text(
                text,
                chat_id=chat_id,
                message_id=message_id,
                parse_mode=ParseMode.HTML,
                reply_markup=markup,
            )
        else:
            await bot.send_message(
                chat_id, text, parse_mode=ParseMode.HTML, reply_markup=markup
            )
    except TelegramBadRequest:
        await bot.send_message(
            chat_id, text, parse_mode=ParseMode.HTML, reply_markup=markup
        )


# ---------- /start ----------


@router.message(CommandStart())
async def cmd_start(message: Message, state: FSMContext) -> None:
    await state.clear()
    uid = message.from_user.id  # type: ignore
    if await CM.is_authorized(uid):
        await show_dashboard(message.bot, message.chat.id, uid)  # type: ignore
        return
    await message.answer(
        WELCOME_TEXT,
        parse_mode=ParseMode.HTML,
        reply_markup=kb([[("🔐 CONNECT ACCOUNT", "auth:connect")]]),
    )


@router.message(Command("dashboard"))
async def cmd_dashboard(message: Message, state: FSMContext) -> None:
    await state.clear()
    await show_dashboard(message.bot, message.chat.id, message.from_user.id)  # type: ignore


@router.message(Command("cancel"))
async def cmd_cancel(message: Message, state: FSMContext) -> None:
    await state.clear()
    await message.answer("Cancelled.", reply_markup=kb([[("« Dashboard", "nav:dashboard")]]))


# ---------- Auth flow ----------


@router.callback_query(F.data == "auth:connect")
async def cb_connect(cq: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await state.set_state(LoginFSM.api_id)
    await cq.message.edit_text(  # type: ignore
        "🔑 <b>Step 1/5 — API ID</b>\n\n"
        "Enter your Telegram <b>API ID</b>\n"
        "(from <code>https://my.telegram.org</code>).\n\n"
        "<i>Send /cancel to abort.</i>",
        parse_mode=ParseMode.HTML,
        reply_markup=cancel_kb("auth:cancel"),
    )
    await cq.answer()


@router.callback_query(F.data == "auth:cancel")
async def cb_auth_cancel(cq: CallbackQuery, state: FSMContext) -> None:
    uid = cq.from_user.id
    await state.clear()
    await CM.disconnect(uid)
    CM.clear_temp_creds(uid)
    await cq.message.edit_text(  # type: ignore
        WELCOME_TEXT,
        parse_mode=ParseMode.HTML,
        reply_markup=kb([[("🔐 CONNECT ACCOUNT", "auth:connect")]]),
    )
    await cq.answer("Cancelled")


@router.message(StateFilter(LoginFSM.api_id))
async def login_api_id(message: Message, state: FSMContext) -> None:
    text = (message.text or "").strip()
    # delete user message to reduce credential exposure in chat
    try:
        await message.delete()
    except Exception:
        pass
    if not text.isdigit():
        await message.answer(
            "❌ API ID must be a number. Try again:",
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    await state.update_data(api_id=int(text))
    await state.set_state(LoginFSM.api_hash)
    await message.answer(
        "🔐 <b>Step 2/5 — API Hash</b>\n\n"
        "Enter your Telegram <b>API Hash</b>.\n"
        "<i>It will not be logged or sent to the log channel.</i>",
        parse_mode=ParseMode.HTML,
        reply_markup=cancel_kb("auth:cancel"),
    )


@router.message(StateFilter(LoginFSM.api_hash))
async def login_api_hash(message: Message, state: FSMContext) -> None:
    api_hash = (message.text or "").strip()
    try:
        await message.delete()
    except Exception:
        pass
    if len(api_hash) < 20 or " " in api_hash:
        await message.answer(
            "❌ Invalid API Hash format. Try again:",
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    await state.update_data(api_hash=api_hash)
    await state.set_state(LoginFSM.phone)
    await message.answer(
        "📱 <b>Step 3/5 — Phone Number</b>\n\n"
        "Enter your Telegram phone number with country code.\n"
        "Example: <code>+14155552671</code>",
        parse_mode=ParseMode.HTML,
        reply_markup=cancel_kb("auth:cancel"),
    )


@router.message(StateFilter(LoginFSM.phone))
async def login_phone(message: Message, state: FSMContext) -> None:
    phone = (message.text or "").strip().replace(" ", "")
    try:
        await message.delete()
    except Exception:
        pass
    if not re.fullmatch(r"\+\d{8,15}", phone):
        await message.answer(
            "❌ Invalid phone. Use international format like <code>+14155552671</code>",
            parse_mode=ParseMode.HTML,
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    data = await state.get_data()
    uid = message.from_user.id  # type: ignore
    status = await message.answer("⏳ Connecting to Telegram…")
    try:
        client = await CM.begin_login(uid, int(data["api_id"]), str(data["api_hash"]))
        await CM.send_code(uid, phone)
    except errors.FloodWaitError as e:
        await status.edit_text(
            f"⏳ FloodWait: retry after {e.seconds}s.",
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    except errors.PhoneNumberInvalidError:
        await status.edit_text(
            "❌ Invalid phone number.",
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    except errors.ApiIdInvalidError:
        await status.edit_text(
            "❌ Invalid API ID / Hash.",
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    except Exception as e:
        log.warning("send_code uid=%s %s", uid, type(e).__name__)
        await status.edit_text(
            f"❌ Could not send code ({type(e).__name__}). Check credentials.",
            reply_markup=cancel_kb("auth:cancel"),
        )
        return

    await state.set_state(LoginFSM.otp)
    # Do not echo phone fully
    await status.edit_text(
        "📩 <b>Step 4/5 — OTP</b>\n\n"
        "Enter the Telegram login code you received.\n"
        "<i>Never share this code. It is not logged.</i>",
        parse_mode=ParseMode.HTML,
        reply_markup=cancel_kb("auth:cancel"),
    )


@router.message(StateFilter(LoginFSM.otp))
async def login_otp(message: Message, state: FSMContext) -> None:
    code = (message.text or "").strip().replace(" ", "").replace("-", "")
    try:
        await message.delete()
    except Exception:
        pass
    # Never log the code
    if not code.isdigit() or not (4 <= len(code) <= 8):
        await message.answer(
            "❌ Invalid code format. Enter the numeric login code:",
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    uid = message.from_user.id  # type: ignore
    status = await message.answer("⏳ Verifying code…")
    result = await CM.sign_in_code(uid, code)
    # wipe local var
    del code

    if result == "ok":
        await state.clear()
        await status.edit_text("✅ <b>ACCOUNT CONNECTED</b>", parse_mode=ParseMode.HTML)
        append_activity(uid, "Account connected")
        await admin_log(message.bot, uid, "✅ Account connected")  # type: ignore
        await show_dashboard(message.bot, message.chat.id, uid)  # type: ignore
        return
    if result == "2fa":
        await state.set_state(LoginFSM.password)
        await status.edit_text(
            "🔒 <b>Step 5/5 — Two-Step Verification</b>\n\n"
            "Enter your Telegram 2FA password.\n"
            "<i>Password is never logged or forwarded.</i>",
            parse_mode=ParseMode.HTML,
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    if result == "invalid_otp":
        await status.edit_text(
            "❌ Invalid OTP. Try again:",
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    if result == "expired_otp":
        await state.clear()
        await CM.disconnect(uid)
        await status.edit_text(
            "❌ Code expired. Start again.",
            reply_markup=kb([[("🔐 CONNECT ACCOUNT", "auth:connect")]]),
        )
        return
    if result.startswith("flood:"):
        sec = result.split(":")[1]
        await status.edit_text(
            f"⏳ FloodWait: retry after {sec}s.",
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    await status.edit_text(
        "❌ Authentication failed. Start again.",
        reply_markup=kb([[("🔐 CONNECT ACCOUNT", "auth:connect")]]),
    )
    await state.clear()


@router.message(StateFilter(LoginFSM.password))
async def login_password(message: Message, state: FSMContext) -> None:
    password = message.text or ""
    try:
        await message.delete()
    except Exception:
        pass
    uid = message.from_user.id  # type: ignore
    status = await message.answer("⏳ Verifying 2FA…")
    result = await CM.sign_in_password(uid, password)
    # wipe
    del password
    if message.text:
        try:
            message.text = None  # type: ignore
        except Exception:
            pass

    if result == "ok":
        await state.clear()
        await status.edit_text("✅ <b>ACCOUNT CONNECTED</b>", parse_mode=ParseMode.HTML)
        append_activity(uid, "Account connected (2FA)")
        await admin_log(message.bot, uid, "✅ Account connected (2FA)")  # type: ignore
        await show_dashboard(message.bot, message.chat.id, uid)  # type: ignore
        return
    if result == "invalid_2fa":
        await status.edit_text(
            "❌ Invalid 2FA password. Try again:",
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    if result.startswith("flood:"):
        sec = result.split(":")[1]
        await status.edit_text(
            f"⏳ FloodWait: retry after {sec}s.",
            reply_markup=cancel_kb("auth:cancel"),
        )
        return
    await state.clear()
    await status.edit_text(
        "❌ 2FA failed. Start again.",
        reply_markup=kb([[("🔐 CONNECT ACCOUNT", "auth:connect")]]),
    )


# ---------- Navigation ----------


@router.callback_query(F.data == "nav:dashboard")
async def nav_dashboard(cq: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await show_dashboard(cq.bot, cq.message.chat.id, cq.from_user.id, cq.message.message_id)  # type: ignore
    await cq.answer()


@router.callback_query(F.data == "nav:cancel")
async def nav_cancel(cq: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await show_dashboard(cq.bot, cq.message.chat.id, cq.from_user.id, cq.message.message_id)  # type: ignore
    await cq.answer("Cancelled")


@router.callback_query(F.data == "nav:logout")
async def nav_logout(cq: CallbackQuery, state: FSMContext) -> None:
    await cq.message.edit_text(  # type: ignore
        "🚪 <b>Logout</b>\n\n"
        "This will disconnect the session and delete local session files for your account.\n"
        "Continue?",
        parse_mode=ParseMode.HTML,
        reply_markup=kb(
            [
                [("✅ Yes, logout", "auth:logout_yes"), ("« Back", "nav:dashboard")],
            ]
        ),
    )
    await cq.answer()


@router.callback_query(F.data == "auth:logout_yes")
async def auth_logout_yes(cq: CallbackQuery, state: FSMContext) -> None:
    uid = cq.from_user.id
    await state.clear()
    await CM.logout_and_wipe(uid)
    cfg = load_user_cfg(uid)
    cfg["selected_channel_id"] = None
    cfg["connected_at"] = None
    cfg["phone_hint"] = None
    save_user_cfg(uid, cfg)
    append_activity(uid, "Account disconnected")
    await admin_log(cq.bot, uid, "🚪 Account disconnected")
    await cq.message.edit_text(  # type: ignore
        "✅ Logged out. Session wiped.\n\n" + WELCOME_TEXT,
        parse_mode=ParseMode.HTML,
        reply_markup=kb([[("🔐 CONNECT ACCOUNT", "auth:connect")]]),
    )
    await cq.answer("Logged out")


@router.callback_query(F.data == "nav:account")
async def nav_account(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    client = await require_auth(uid, cq)
    if not client:
        return
    cfg = load_user_cfg(uid)
    me = await client.get_me()
    name = " ".join(x for x in (me.first_name, me.last_name) if x) or "—"
    uname = f"@{me.username}" if me.username else "—"
    text = (
        "╭━━〔 🔐 ACCOUNT 〕━━╮\n"
        f"┃ Name: <b>{html.escape(name)}</b>\n"
        f"┃ Username: <code>{html.escape(uname)}</code>\n"
        f"┃ User ID: <code>{me.id}</code>\n"
        f"┃ Phone: <code>{cfg.get('phone_hint') or 'Hidden'}</code>\n"
        f"┃ Connected: <code>{cfg.get('connected_at') or '—'}</code>\n"
        f"┃ Session: <b>Isolated / local</b>\n"
        "╰━━━━━━━━━━━━━━━━━━╯"
    )
    await cq.message.edit_text(  # type: ignore
        text,
        parse_mode=ParseMode.HTML,
        reply_markup=back_dash_kb([[("🚪 Logout", "nav:logout")]]),
    )
    await cq.answer()


# ---------- Channels ----------


@router.callback_query(F.data == "nav:channels")
async def nav_channels(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    client = await require_auth(uid, cq)
    if not client:
        return
    await cq.message.edit_text("⏳ Scanning channels…", parse_mode=ParseMode.HTML)  # type: ignore
    try:
        channels = await list_admin_channels(client)
    except errors.FloodWaitError as e:
        await cq.message.edit_text(  # type: ignore
            f"⏳ FloodWait {e.seconds}s. Try again later.",
            reply_markup=back_dash_kb(),
        )
        await cq.answer()
        return
    except Exception as e:
        await cq.message.edit_text(  # type: ignore
            f"❌ Failed to list channels ({type(e).__name__}).",
            reply_markup=back_dash_kb(),
        )
        await cq.answer()
        return

    # cache in memory file
    cache_path = user_dir(uid) / "channels_cache.json"
    with open(cache_path, "w", encoding="utf-8") as f:
        json.dump(channels, f)

    await _render_channel_page(cq, channels, page=0)
    await cq.answer()


@router.callback_query(F.data.startswith("chpage:"))
async def ch_page(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    page = int(cq.data.split(":")[1])  # type: ignore
    cache_path = user_dir(uid) / "channels_cache.json"
    if not cache_path.exists():
        await nav_channels(cq)
        return
    with open(cache_path, "r", encoding="utf-8") as f:
        channels = json.load(f)
    await _render_channel_page(cq, channels, page=page)
    await cq.answer()


async def _render_channel_page(
    cq: CallbackQuery, channels: List[Dict[str, Any]], page: int
) -> None:
    if not channels:
        await cq.message.edit_text(  # type: ignore
            "📡 <b>SELECT CHANNEL</b>\n\n"
            "No channels/groups found where this account has admin rights.",
            parse_mode=ParseMode.HTML,
            reply_markup=back_dash_kb([[("🔄 Refresh", "nav:channels")]]),
        )
        return
    total_pages = max(1, (len(channels) + CHANNEL_PAGE_SIZE - 1) // CHANNEL_PAGE_SIZE)
    page = max(0, min(page, total_pages - 1))
    start = page * CHANNEL_PAGE_SIZE
    chunk = channels[start : start + CHANNEL_PAGE_SIZE]
    rows: List[List[Tuple[str, str]]] = []
    for ch in chunk:
        kind = "📢" if ch.get("broadcast") else "👥"
        title = (ch.get("title") or str(ch["id"]))[:40]
        rows.append([(f"{kind} {title}", f"chsel:{ch['id']}")])
    nav_row: List[Tuple[str, str]] = []
    if page > 0:
        nav_row.append(("« Prev", f"chpage:{page - 1}"))
    nav_row.append((f"{page + 1}/{total_pages}", "noop"))
    if page < total_pages - 1:
        nav_row.append(("Next »", f"chpage:{page + 1}"))
    rows.append(nav_row)
    rows.append([("🔄 Refresh", "nav:channels"), ("« Dashboard", "nav:dashboard")])
    await cq.message.edit_text(  # type: ignore
        "📡 <b>SELECT CHANNEL</b>\n\n"
        f"Found <b>{len(channels)}</b> admin channel(s)/group(s).\n"
        "Tap to connect:",
        parse_mode=ParseMode.HTML,
        reply_markup=kb(rows),
    )


@router.callback_query(F.data == "noop")
async def noop_cb(cq: CallbackQuery) -> None:
    await cq.answer()


@router.callback_query(F.data.startswith("chsel:"))
async def ch_select(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    client = await require_auth(uid, cq)
    if not client:
        return
    cid = int(cq.data.split(":")[1])  # type: ignore
    try:
        entity = await resolve_channel(client, cid)
    except Exception as e:
        await cq.answer(f"Cannot open channel: {type(e).__name__}", show_alert=True)
        return
    cfg = load_user_cfg(uid)
    cfg["selected_channel_id"] = cid
    save_user_cfg(uid, cfg)
    title = html.escape(getattr(entity, "title", str(cid)) or str(cid))
    uname = getattr(entity, "username", None)
    uname_s = f"@{uname}" if uname else "—"
    creator = bool(getattr(entity, "creator", False))
    rights = getattr(entity, "admin_rights", None)
    rlist = []
    if creator:
        rlist.append("creator")
    if rights:
        for attr in (
            "ban_users",
            "delete_messages",
            "invite_users",
            "pin_messages",
            "add_admins",
        ):
            if getattr(rights, attr, False):
                rlist.append(attr)
    rights_s = ", ".join(rlist) if rlist else "admin"
    text = (
        "🟢 <b>CHANNEL CONNECTED</b>\n\n"
        f"📛 Name: <b>{title}</b>\n"
        f"🆔 ID: <code>{cid}</code>\n"
        f"🔗 Username: <code>{html.escape(uname_s)}</code>\n"
        f"🛡 Status: <b>{'Creator' if creator else 'Admin'}</b>\n"
        f"✅ Permissions: <code>{html.escape(rights_s)}</code>"
    )
    append_activity(uid, f"Channel selected: {cid}")
    await admin_log(cq.bot, uid, f"📡 Channel selected: <code>{cid}</code>")
    await cq.message.edit_text(  # type: ignore
        text,
        parse_mode=ParseMode.HTML,
        reply_markup=back_dash_kb(
            [[("👥 Members", "nav:members"), ("📊 Stats", "nav:stats")]]
        ),
    )
    await cq.answer("Channel connected")


# ---------- Members ----------


@router.callback_query(F.data == "nav:members")
async def nav_members(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    client = await require_auth(uid, cq)
    if not client:
        return
    cid = await require_channel(uid, cq)
    if not cid:
        return
    await _render_members(cq, client, cid, offset=0)
    await cq.answer()


@router.callback_query(F.data.startswith("mpage:"))
async def members_page(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    client = await require_auth(uid, cq)
    if not client:
        return
    cid = await require_channel(uid, cq)
    if not cid:
        return
    offset = int(cq.data.split(":")[1])  # type: ignore
    await _render_members(cq, client, cid, offset=offset)
    await cq.answer()


async def _render_members(
    cq: CallbackQuery, client: TelegramClient, cid: int, offset: int
) -> None:
    try:
        channel = await resolve_channel(client, cid)
    except Exception as e:
        await cq.message.edit_text(  # type: ignore
            f"❌ Channel error: {type(e).__name__}",
            reply_markup=back_dash_kb(),
        )
        return
    members, has_more = await iter_members_page(
        client, channel, offset=offset, limit=MEMBER_PAGE_SIZE
    )
    title = html.escape(getattr(channel, "title", str(cid)) or str(cid))
    lines = [
        "👥 <b>MEMBERS</b>",
        f"Channel: <b>{title}</b>",
        f"Offset: <code>{offset}</code>",
        "",
    ]
    rows: List[List[Tuple[str, str]]] = []
    if not members:
        lines.append("<i>No members on this page (or insufficient rights to list).</i>")
    else:
        for m in members:
            un = f"@{m['username']}" if m.get("username") else "—"
            flag = "🤖" if m.get("bot") else "👤"
            lines.append(
                f"{flag} <b>{html.escape(m['name'])}</b> · "
                f"<code>{m['id']}</code> · {html.escape(un)}"
            )
            rows.append(
                [
                    (f"ℹ {m['id']}", f"minfo:{m['id']}"),
                    ("🗑", f"mrm:{m['id']}"),
                ]
            )
    nav_row: List[Tuple[str, str]] = []
    if offset > 0:
        prev_off = max(0, offset - MEMBER_PAGE_SIZE)
        nav_row.append(("« Prev", f"mpage:{prev_off}"))
    if has_more:
        nav_row.append(("Next »", f"mpage:{offset + MEMBER_PAGE_SIZE}"))
    if nav_row:
        rows.append(nav_row)
    rows.append(
        [
            ("🔎 Search", "nav:search"),
            ("🔄 Refresh", f"mpage:{offset}"),
        ]
    )
    rows.append([("« Dashboard", "nav:dashboard")])
    await cq.message.edit_text(  # type: ignore
        "\n".join(lines),
        parse_mode=ParseMode.HTML,
        reply_markup=kb(rows),
    )


@router.callback_query(F.data.startswith("minfo:"))
async def member_info(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    client = await require_auth(uid, cq)
    if not client:
        return
    cid = await require_channel(uid, cq)
    if not cid:
        return
    user_id = int(cq.data.split(":")[1])  # type: ignore
    try:
        channel = await resolve_channel(client, cid)
        ent = await client.get_entity(user_id)
        if not isinstance(ent, User):
            await cq.answer("Not a user", show_alert=True)
            return
        m = _user_dict(ent)
        participant = None
        try:
            participant = await client.get_permissions(channel, ent)
        except Exception:
            pass
        role = "member"
        if participant:
            if participant.is_creator:
                role = "creator"
            elif participant.is_admin:
                role = "admin"
            elif participant.is_banned:
                role = "restricted/banned"
        un = f"@{m['username']}" if m.get("username") else "—"
        text = (
            "👤 <b>MEMBER DETAILS</b>\n\n"
            f"Name: <b>{html.escape(m['name'])}</b>\n"
            f"ID: <code>{m['id']}</code>\n"
            f"Username: <code>{html.escape(un)}</code>\n"
            f"Role: <b>{role}</b>\n"
            f"Bot: <b>{'yes' if m['bot'] else 'no'}</b>\n"
            f"Premium: <b>{'yes' if m.get('premium') else 'no'}</b>\n"
            f"Restricted: <b>{'yes' if m.get('restricted') else 'no'}</b>\n"
        )
        rows = [
            [("🗑 Remove", f"mrm:{m['id']}"), ("✅ Unban", f"munban:{m['id']}")],
            [("« Members", "nav:members"), ("« Dashboard", "nav:dashboard")],
        ]
        await cq.message.edit_text(text, parse_mode=ParseMode.HTML, reply_markup=kb(rows))  # type: ignore
        await cq.answer()
    except Exception as e:
        await cq.answer(f"Error: {type(e).__name__}", show_alert=True)


@router.callback_query(F.data.startswith("mrm:"))
async def member_remove_confirm(cq: CallbackQuery, state: FSMContext) -> None:
    user_id = int(cq.data.split(":")[1])  # type: ignore
    await state.update_data(remove_user_id=user_id)
    await cq.message.edit_text(  # type: ignore
        f"🗑 <b>Remove member</b>\n\n"
        f"User ID: <code>{user_id}</code>\n"
        "This uses your account's admin rights (ban/restrict view).\n"
        "Confirm?",
        parse_mode=ParseMode.HTML,
        reply_markup=kb(
            [
                [("✅ Confirm remove", f"mrmyes:{user_id}")],
                [("« Cancel", "nav:members")],
            ]
        ),
    )
    await cq.answer()


@router.callback_query(F.data.startswith("mrmyes:"))
async def member_remove_yes(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    client = await require_auth(uid, cq)
    if not client:
        return
    cid = await require_channel(uid, cq)
    if not cid:
        return
    user_id = int(cq.data.split(":")[1])  # type: ignore
    try:
        channel = await resolve_channel(client, cid)
        ok = await remove_member(client, channel, user_id)
        if ok:
            append_activity(uid, f"Removed member {user_id} from {cid}")
            await admin_log(
                cq.bot, uid, f"🗑 Removed member <code>{user_id}</code> from <code>{cid}</code>"
            )
            await cq.message.edit_text(  # type: ignore
                f"✅ Member <code>{user_id}</code> removed (or restricted).",
                parse_mode=ParseMode.HTML,
                reply_markup=back_dash_kb([[("« Members", "nav:members")]]),
            )
        else:
            await cq.message.edit_text(  # type: ignore
                f"❌ Could not remove <code>{user_id}</code>. "
                "Check admin rights / target role.",
                parse_mode=ParseMode.HTML,
                reply_markup=back_dash_kb([[("« Members", "nav:members")]]),
            )
    except errors.FloodWaitError as e:
        await cq.message.edit_text(  # type: ignore
            f"⏳ FloodWait {e.seconds}s.",
            reply_markup=back_dash_kb(),
        )
    except Exception as e:
        await cq.message.edit_text(  # type: ignore
            f"❌ Error: {type(e).__name__}",
            reply_markup=back_dash_kb(),
        )
    await cq.answer()


@router.callback_query(F.data.startswith("munban:"))
async def member_unban(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    client = await require_auth(uid, cq)
    if not client:
        return
    cid = await require_channel(uid, cq)
    if not cid:
        return
    user_id = int(cq.data.split(":")[1])  # type: ignore
    try:
        channel = await resolve_channel(client, cid)
        ok = await unban_member(client, channel, user_id)
        msg = "✅ Permissions restored." if ok else "❌ Could not unban/restore."
        await cq.message.edit_text(  # type: ignore
            msg,
            reply_markup=back_dash_kb([[("« Members", "nav:members")]]),
        )
        if ok:
            append_activity(uid, f"Unbanned {user_id} on {cid}")
            await admin_log(cq.bot, uid, f"✅ Unban <code>{user_id}</code> on <code>{cid}</code>")
    except errors.FloodWaitError as e:
        await cq.answer(f"FloodWait {e.seconds}s", show_alert=True)
        return
    except Exception as e:
        await cq.answer(type(e).__name__, show_alert=True)
        return
    await cq.answer()


# ---------- Search ----------


@router.callback_query(F.data == "nav:search")
async def nav_search(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if not await require_auth(uid, cq):
        return
    if not await require_channel(uid, cq):
        return
    await cq.message.edit_text(  # type: ignore
        "🔎 <b>SEARCH MEMBER</b>\n\nChoose mode:",
        parse_mode=ParseMode.HTML,
        reply_markup=kb(
            [
                [("🆔 By user ID", "search:id"), ("@ By username", "search:user")],
                [("🔤 Text search", "search:text")],
                [("« Dashboard", "nav:dashboard")],
            ]
        ),
    )
    await cq.answer()


@router.callback_query(F.data == "search:id")
async def search_id_start(cq: CallbackQuery, state: FSMContext) -> None:
    await state.set_state(SearchFSM.by_id)
    await cq.message.edit_text(  # type: ignore
        "🆔 Send the numeric <b>user ID</b>:",
        parse_mode=ParseMode.HTML,
        reply_markup=cancel_kb(),
    )
    await cq.answer()


@router.callback_query(F.data == "search:user")
async def search_user_start(cq: CallbackQuery, state: FSMContext) -> None:
    await state.set_state(SearchFSM.by_username)
    await cq.message.edit_text(  # type: ignore
        "@ Send the <b>username</b> (with or without @):",
        parse_mode=ParseMode.HTML,
        reply_markup=cancel_kb(),
    )
    await cq.answer()


@router.callback_query(F.data == "search:text")
async def search_text_start(cq: CallbackQuery, state: FSMContext) -> None:
    await state.set_state(SearchFSM.query)
    await cq.message.edit_text(  # type: ignore
        "🔤 Send a name fragment to search among participants:",
        parse_mode=ParseMode.HTML,
        reply_markup=cancel_kb(),
    )
    await cq.answer()


async def _do_search(message: Message, state: FSMContext, query: str) -> None:
    uid = message.from_user.id  # type: ignore
    await state.clear()
    client = await CM.ensure_client(uid)
    if not client:
        await message.answer("Not connected.", reply_markup=kb([[("🔐 CONNECT", "auth:connect")]]))
        return
    cfg = load_user_cfg(uid)
    cid = cfg.get("selected_channel_id")
    if not cid:
        await message.answer("No channel selected.", reply_markup=kb([[("📡 CHANNELS", "nav:channels")]]))
        return
    try:
        channel = await resolve_channel(client, int(cid))
        m = await find_user(client, channel, query)
    except errors.FloodWaitError as e:
        await message.answer(f"⏳ FloodWait {e.seconds}s")
        return
    except Exception as e:
        await message.answer(f"❌ {type(e).__name__}")
        return
    if not m:
        await message.answer(
            "❌ User not found.",
            reply_markup=back_dash_kb([[("🔎 Search again", "nav:search")]]),
        )
        return
    un = f"@{m['username']}" if m.get("username") else "—"
    text = (
        "🔎 <b>SEARCH RESULT</b>\n\n"
        f"Name: <b>{html.escape(m['name'])}</b>\n"
        f"ID: <code>{m['id']}</code>\n"
        f"Username: <code>{html.escape(un)}</code>\n"
    )
    await message.answer(
        text,
        parse_mode=ParseMode.HTML,
        reply_markup=kb(
            [
                [("ℹ Details", f"minfo:{m['id']}"), ("🗑 Remove", f"mrm:{m['id']}")],
                [("🔎 Search", "nav:search"), ("« Dashboard", "nav:dashboard")],
            ]
        ),
    )


@router.message(StateFilter(SearchFSM.by_id))
async def search_id_msg(message: Message, state: FSMContext) -> None:
    await _do_search(message, state, (message.text or "").strip())


@router.message(StateFilter(SearchFSM.by_username))
async def search_un_msg(message: Message, state: FSMContext) -> None:
    await _do_search(message, state, (message.text or "").strip())


@router.message(StateFilter(SearchFSM.query))
async def search_q_msg(message: Message, state: FSMContext) -> None:
    await _do_search(message, state, (message.text or "").strip())


# ---------- Member management menu ----------


@router.callback_query(F.data == "nav:mmgmt")
async def nav_mmgmt(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if not await require_auth(uid, cq):
        return
    if not await require_channel(uid, cq):
        return
    await cq.message.edit_text(  # type: ignore
        "🗑 <b>MEMBER MANAGEMENT</b>\n\n"
        "Actions use your connected account's admin permissions only.",
        parse_mode=ParseMode.HTML,
        reply_markup=kb(
            [
                [("👥 Browse members", "nav:members")],
                [("🔎 Search member", "nav:search")],
                [("⚡ Bulk remove by IDs", "bulk:remove_ids")],
                [("« Dashboard", "nav:dashboard")],
            ]
        ),
    )
    await cq.answer()


# ---------- Bulk ----------


@router.callback_query(F.data == "nav:bulk")
async def nav_bulk(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if not await require_auth(uid, cq):
        return
    if not await require_channel(uid, cq):
        return
    job = BULK.get(uid)
    running = job and not job.stats.finished and not job.stats.stopped
    lines = [
        "⚡ <b>BULK ACTION</b>\n",
        "Legitimate API-supported operations only.",
        "Bounded workers · FloodWait aware · STOP supported.\n",
    ]
    if running:
        lines.append("⚠️ A job is currently running.")
    await cq.message.edit_text(  # type: ignore
        "\n".join(lines),
        parse_mode=ParseMode.HTML,
        reply_markup=kb(
            [
                [("🗑 Bulk remove (paste IDs)", "bulk:remove_ids")],
                [("⛔ STOP NOW", "bulk:stop")] if running else [("✅ Unban (paste IDs)", "bulk:unban_ids")],
                [("« Dashboard", "nav:dashboard")],
            ]
        ),
    )
    await cq.answer()


@router.callback_query(F.data.in_({"bulk:remove_ids", "bulk:unban_ids"}))
async def bulk_ids_start(cq: CallbackQuery, state: FSMContext) -> None:
    uid = cq.from_user.id
    if not await require_auth(uid, cq):
        return
    if not await require_channel(uid, cq):
        return
    action = "remove" if cq.data == "bulk:remove_ids" else "unban"
    await state.set_state(BulkFSM.input_ids)
    await state.update_data(bulk_action=action)
    await cq.message.edit_text(  # type: ignore
        f"⚡ <b>Bulk {action}</b>\n\n"
        "Send user IDs separated by comma, space, or newline.\n"
        "Example: <code>12345 67890 111</code>\n\n"
        f"Max recommended batch: 500. Workers limited to {MAX_CONCURRENT_WORKERS}.",
        parse_mode=ParseMode.HTML,
        reply_markup=cancel_kb(),
    )
    await cq.answer()


@router.message(StateFilter(BulkFSM.input_ids))
async def bulk_ids_input(message: Message, state: FSMContext) -> None:
    uid = message.from_user.id  # type: ignore
    data = await state.get_data()
    action = data.get("bulk_action") or "remove"
    await state.clear()
    raw = message.text or ""
    ids: List[int] = []
    for part in re.split(r"[\s,;]+", raw.strip()):
        if re.fullmatch(r"-?\d+", part):
            ids.append(int(part))
    # unique preserve order
    seen: Set[int] = set()
    uniq: List[int] = []
    for i in ids:
        if i not in seen:
            seen.add(i)
            uniq.append(i)
    if not uniq:
        await message.answer(
            "❌ No valid user IDs found.",
            reply_markup=back_dash_kb([[("⚡ Bulk", "nav:bulk")]]),
        )
        return
    if len(uniq) > 2000:
        uniq = uniq[:2000]
    cfg = load_user_cfg(uid)
    workers = int(cfg.get("workers") or DEFAULT_WORKERS)
    workers = max(1, min(MAX_CONCURRENT_WORKERS, workers))

    async def worker_fn(client: TelegramClient, item: Any, job: BulkJob) -> bool:
        channel = await resolve_channel(client, int(cfg["selected_channel_id"]))
        if action == "remove":
            return await remove_member(client, channel, int(item))
        return await unban_member(client, channel, int(item))

    job = BulkJob(
        uid=uid,
        name=f"bulk_{action}",
        items=uniq,
        worker_fn=worker_fn,
        workers=workers,
    )
    status = await message.answer(
        "╭━━〔 ⚡ OPERATION RUNNING 〕━━╮\n"
        "┃ Starting…\n"
        "╰━━━━━━━━━━━━━━━━━━━━━━━━━━╯",
        reply_markup=kb([[("⛔ STOP NOW", "bulk:stop")]]),
    )
    append_activity(uid, f"Bulk {action} started ({len(uniq)} ids)")
    await admin_log(
        message.bot,  # type: ignore
        uid,
        f"⚡ Bulk <b>{html.escape(action)}</b> started · {len(uniq)} ids",
    )

    async def _run() -> None:
        stats = await BULK.run(message.bot, job, status.chat.id, status.message_id)  # type: ignore
        append_activity(
            uid,
            f"Bulk {action} finished ok={stats.success} fail={stats.failed} stop={stats.stopped}",
        )
        await admin_log(
            message.bot,  # type: ignore
            uid,
            f"⚡ Bulk <b>{html.escape(action)}</b> done · "
            f"ok={stats.success} fail={stats.failed} stopped={stats.stopped}",
        )

    asyncio.create_task(_run())


@router.callback_query(F.data == "bulk:stop")
async def bulk_stop(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    job = await BULK.stop(uid)
    if not job:
        await cq.answer("No running operation", show_alert=True)
        return
    await cq.answer("Stopping…")
    append_activity(uid, "Bulk STOP requested")
    await admin_log(cq.bot, uid, "⛔ Bulk STOP requested")


# ---------- Statistics ----------


@router.callback_query(F.data == "nav:stats")
async def nav_stats(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    client = await require_auth(uid, cq)
    if not client:
        return
    cid = await require_channel(uid, cq)
    if not cid:
        return
    await cq.message.edit_text("⏳ Loading statistics…")  # type: ignore
    try:
        channel = await resolve_channel(client, cid)
        count = await get_member_count(client, channel)
        title = html.escape(getattr(channel, "title", str(cid)) or str(cid))
        uname = getattr(channel, "username", None)
        uname_s = f"@{uname}" if uname else "—"
        kind = "Channel" if getattr(channel, "broadcast", False) else "Group"
        text = (
            "📊 <b>STATISTICS</b>\n\n"
            f"📛 {title}\n"
            f"🏷 Type: <b>{kind}</b>\n"
            f"🆔 <code>{cid}</code>\n"
            f"🔗 <code>{html.escape(uname_s)}</code>\n"
            f"👥 Members (approx): <b>{count}</b>\n"
        )
        job = BULK.get(uid)
        if job:
            s = job.stats
            text += (
                "\n⚡ <b>Last / current bulk</b>\n"
                f"Processed: {s.processed}/{s.total}\n"
                f"Success: {s.success} · Failed: {s.failed}\n"
                f"FloodWaits: {s.flood_waits}\n"
                f"Finished: {s.finished} · Stopped: {s.stopped}\n"
            )
        await cq.message.edit_text(  # type: ignore
            text,
            parse_mode=ParseMode.HTML,
            reply_markup=back_dash_kb([[("🔄 Refresh", "nav:stats")]]),
        )
    except errors.FloodWaitError as e:
        await cq.message.edit_text(  # type: ignore
            f"⏳ FloodWait {e.seconds}s",
            reply_markup=back_dash_kb(),
        )
    except Exception as e:
        await cq.message.edit_text(  # type: ignore
            f"❌ {type(e).__name__}",
            reply_markup=back_dash_kb(),
        )
    await cq.answer()


# ---------- Activity ----------


@router.callback_query(F.data == "nav:activity")
async def nav_activity(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if not await require_auth(uid, cq):
        return
    cfg = load_user_cfg(uid)
    acts = list(reversed(cfg.get("activity") or []))[:30]
    if not acts:
        body = "<i>No activity yet.</i>"
    else:
        lines = []
        for a in acts:
            ts = (a.get("ts") or "")[:19].replace("T", " ")
            ev = html.escape(str(a.get("event") or ""))
            lines.append(f"• <code>{ts}</code> — {ev}")
        body = "\n".join(lines)
    await cq.message.edit_text(  # type: ignore
        f"📝 <b>ACTIVITY LOGS</b>\n\n{body}",
        parse_mode=ParseMode.HTML,
        reply_markup=back_dash_kb(),
    )
    await cq.answer()


# ---------- Settings ----------


@router.callback_query(F.data == "nav:settings")
async def nav_settings(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    if not await require_auth(uid, cq):
        return
    cfg = load_user_cfg(uid)
    log_ch = cfg.get("log_channel_id") or "Not set"
    workers = cfg.get("workers") or DEFAULT_WORKERS
    text = (
        "⚙️ <b>SETTINGS</b>\n\n"
        f"📋 Private log channel: <code>{html.escape(str(log_ch))}</code>\n"
        f"👷 Bulk workers: <b>{workers}</b> (max {MAX_CONCURRENT_WORKERS})\n\n"
        "<i>Log channel receives operational events only — "
        "never OTP, 2FA, API hash, or session data.</i>"
    )
    await cq.message.edit_text(  # type: ignore
        text,
        parse_mode=ParseMode.HTML,
        reply_markup=kb(
            [
                [("📋 Set log channel", "set:logch"), ("👷 Set workers", "set:workers")],
                [("🧹 Clear log channel", "set:logch_clear")],
                [("« Dashboard", "nav:dashboard")],
            ]
        ),
    )
    await cq.answer()


@router.callback_query(F.data == "set:logch")
async def set_logch(cq: CallbackQuery, state: FSMContext) -> None:
    await state.set_state(SettingsFSM.log_channel)
    await cq.message.edit_text(  # type: ignore
        "📋 Send the <b>private channel ID</b> (e.g. <code>-100xxxxxxxxxx</code>).\n"
        "Add this bot as admin in that channel so it can post logs.\n\n"
        "Or forward a message from the channel and send its chat id.",
        parse_mode=ParseMode.HTML,
        reply_markup=cancel_kb(),
    )
    await cq.answer()


@router.message(StateFilter(SettingsFSM.log_channel))
async def set_logch_msg(message: Message, state: FSMContext) -> None:
    uid = message.from_user.id  # type: ignore
    await state.clear()
    text = (message.text or "").strip()
    if not re.fullmatch(r"-?\d+", text):
        await message.answer(
            "❌ Invalid channel ID.",
            reply_markup=back_dash_kb([[("⚙️ Settings", "nav:settings")]]),
        )
        return
    ch_id = int(text)
    # probe
    try:
        await message.bot.send_message(  # type: ignore
            ch_id,
            f"📋 Log channel linked by user <code>{uid}</code>.",
            parse_mode=ParseMode.HTML,
        )
    except Exception as e:
        await message.answer(
            f"❌ Cannot post to that chat ({type(e).__name__}). "
            "Add the bot as admin and try again.",
            reply_markup=back_dash_kb([[("⚙️ Settings", "nav:settings")]]),
        )
        return
    cfg = load_user_cfg(uid)
    cfg["log_channel_id"] = ch_id
    save_user_cfg(uid, cfg)
    append_activity(uid, f"Log channel set to {ch_id}")
    await admin_log(message.bot, uid, "⚙️ Log channel configured")  # type: ignore
    await message.answer(
        "✅ Log channel saved.",
        reply_markup=back_dash_kb([[("⚙️ Settings", "nav:settings")]]),
    )


@router.callback_query(F.data == "set:logch_clear")
async def set_logch_clear(cq: CallbackQuery) -> None:
    uid = cq.from_user.id
    cfg = load_user_cfg(uid)
    cfg["log_channel_id"] = None
    save_user_cfg(uid, cfg)
    append_activity(uid, "Log channel cleared")
    await cq.answer("Cleared")
    await nav_settings(cq)


@router.callback_query(F.data == "set:workers")
async def set_workers(cq: CallbackQuery, state: FSMContext) -> None:
    await state.set_state(SettingsFSM.workers)
    await cq.message.edit_text(  # type: ignore
        f"👷 Send worker count (1–{MAX_CONCURRENT_WORKERS}).\n"
        "Lower is safer for FloodWait.",
        reply_markup=cancel_kb(),
    )
    await cq.answer()


@router.message(StateFilter(SettingsFSM.workers))
async def set_workers_msg(message: Message, state: FSMContext) -> None:
    uid = message.from_user.id  # type: ignore
    await state.clear()
    text = (message.text or "").strip()
    if not text.isdigit():
        await message.answer("❌ Enter a number.", reply_markup=back_dash_kb())
        return
    n = int(text)
    n = max(1, min(MAX_CONCURRENT_WORKERS, n))
    cfg = load_user_cfg(uid)
    cfg["workers"] = n
    save_user_cfg(uid, cfg)
    append_activity(uid, f"Workers set to {n}")
    await admin_log(message.bot, uid, f"⚙️ Workers set to {n}")  # type: ignore
    await message.answer(
        f"✅ Workers set to <b>{n}</b>.",
        parse_mode=ParseMode.HTML,
        reply_markup=back_dash_kb([[("⚙️ Settings", "nav:settings")]]),
    )


# ---------- Fallback ----------


@router.message()
async def fallback_msg(message: Message, state: FSMContext) -> None:
    cur = await state.get_state()
    if cur:
        return
    await message.answer(
        "Use /start or open the dashboard.",
        reply_markup=kb([[("🏠 Dashboard", "nav:dashboard")]]),
    )


@router.callback_query()
async def fallback_cb(cq: CallbackQuery) -> None:
    await cq.answer("Unknown action", show_alert=False)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


async def on_shutdown(bot: Bot) -> None:
    log.info("Shutting down — disconnecting clients…")
    uids = list(CM._clients.keys())
    for uid in uids:
        try:
            await CM.disconnect(uid)
        except Exception:
            pass
    await bot.session.close()


async def main() -> None:
    bot = Bot(token=BOT_TOKEN)
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)
    dp.shutdown.register(on_shutdown)

    me = await bot.get_me()
    log.info("Bot started as @%s (id=%s)", me.username, me.id)
    log.info("Data directory: %s", DATA_DIR)

    # Restore nothing eagerly — sessions load on demand per user
    try:
        await dp.start_polling(bot, allowed_updates=dp.resolve_used_update_types())
    finally:
        await on_shutdown(bot)


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print("\nBye.")
