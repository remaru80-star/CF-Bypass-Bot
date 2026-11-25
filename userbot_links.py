"""Userbot link generation: file -> link bot 1 -> (link bot 2).

Flow (one userbot session, one job at a time):
  bot1: /start, /universal_link, click "Single Message Link", send the file  -> bot1 replies with a link
  bot2: /start, send bot1's link                                            -> bot2 replies with a link
The userbot account must be a member of the FILE channel (it copies the file from there).
"""
import asyncio
import re

from pyrogram import Client
from pyrogram.errors import (PasswordHashInvalid, PhoneCodeExpired, PhoneCodeInvalid, PhoneNumberInvalid,
                             SessionPasswordNeeded)
from pyrogram.handlers import EditedMessageHandler, MessageHandler

LINK_CMD = "/universal_link"          # change here if the bot really uses /universal_link
MENU_BUTTON = "Single Message Link"
URL_RE = re.compile(r"https?://[^\s\)\]>\"']+")

_clients: dict = {}
_queues: dict = {}
_locks: dict = {}


async def get_userbot(session, api_id, api_hash):
    ub = _clients.get(session)
    if ub:
        return ub
    ub = Client(f"ub_{abs(hash(session))}", api_id=api_id, api_hash=api_hash,
                session_string=session, in_memory=True)

    async def _on_msg(_, m):
        if m.outgoing:
            return
        q = _queues.get((session, m.chat.id))
        if q is not None:
            q.put_nowait(m)

    ub.add_handler(MessageHandler(_on_msg))
    ub.add_handler(EditedMessageHandler(_on_msg))
    await ub.start()
    _clients[session] = ub
    _locks[session] = asyncio.Lock()
    return ub


IGNORE = ("t.me/share", "telegra.ph", "graph.org")   # share button + the tutorial link ("To know more click here")


def all_links(m):
    text = m.text or m.caption or ""
    out = [getattr(e, "url", None) for e in (m.entities or m.caption_entities or [])]
    out += URL_RE.findall(text)
    for row in (getattr(m.reply_markup, "inline_keyboard", None) or []):
        out += [b.url for b in row if b.url]
    return [x for x in out if x and not any(s in x for s in IGNORE)]


def extract_link(m, want=None):
    """First real link in the message. want="start=" keeps only the file-share deep link (t.me/<bot>?start=...)."""
    links = [x for x in all_links(m) if not want or want in x]
    return links[0] if links else None


def _button(m, label):
    for row in (getattr(m.reply_markup, "inline_keyboard", None) or []):
        for b in row:
            if label.lower() in (b.text or "").lower():
                return b.text
    return None


async def _wait(q, pred, timeout):
    loop = asyncio.get_running_loop()
    end = loop.time() + timeout
    while True:
        left = end - loop.time()
        if left <= 0:
            raise asyncio.TimeoutError
        m = await asyncio.wait_for(q.get(), left)
        if pred(m):
            return m


def _drain(q):
    while not q.empty():
        q.get_nowait()


async def drop_userbot(session):
    ub = _clients.pop(session, None)
    _locks.pop(session, None)
    if ub:
        try:
            await ub.stop()
        except Exception:
            pass


# ---------------- login by phone number (code, then the 2FA password if the account has one)
class LoginError(Exception):
    def __init__(self, msg, retry=False):
        super().__init__(msg)
        self.retry = retry


_pending: dict = {}   # admin id -> (client, phone, phone_code_hash)


async def login_cancel(uid):
    p = _pending.pop(uid, None)
    if p:
        try:
            await p[0].disconnect()
        except Exception:
            pass


async def login_start(uid, phone, api_id, api_hash):
    await login_cancel(uid)
    c = Client(f"login_{uid}", api_id=api_id, api_hash=api_hash, in_memory=True)
    try:
        await c.connect()
        sent = await c.send_code(phone)
    except PhoneNumberInvalid:
        await c.disconnect()
        raise LoginError("That phone number is invalid. Send it with the country code, e.g. +919876543210.", retry=True)
    except Exception as e:
        try:
            await c.disconnect()
        except Exception:
            pass
        raise LoginError(f"Could not send the code: {str(e)[:150]}")
    _pending[uid] = (c, phone, sent.phone_code_hash)


async def _finish(uid):
    c = _pending.pop(uid)[0]
    try:
        me = await c.get_me()
        session = await c.export_session_string()
    finally:
        await c.disconnect()
    return "ok", session, me


async def login_code(uid, code):
    p = _pending.get(uid)
    if not p:
        raise LoginError("The login expired.")
    c, phone, h = p
    try:
        await c.sign_in(phone, h, code)
    except SessionPasswordNeeded:
        return "password",
    except PhoneCodeInvalid:
        raise LoginError("Wrong code.", retry=True)
    except PhoneCodeExpired:
        await login_cancel(uid)
        raise LoginError("The code expired (Telegram cancels codes that are typed inside Telegram). Log in from the terminal instead: python3 login_userbot.py")
    except Exception as e:
        await login_cancel(uid)
        raise LoginError(str(e)[:150])
    return await _finish(uid)


async def login_password(uid, password):
    p = _pending.get(uid)
    if not p:
        raise LoginError("The login expired.")
    try:
        await p[0].check_password(password)
    except PasswordHashInvalid:
        raise LoginError("Wrong password.", retry=True)
    except Exception as e:
        await login_cancel(uid)
        raise LoginError(str(e)[:150])
    return await _finish(uid)


async def generate_links(session, api_id, api_hash, bot1, bot2, file_chat_id, file_msg_id, timeout=180):
    """Returns (link1, link2). link2 is None when bot2 is not set."""
    ub = await get_userbot(session, api_id, api_hash)
    async with _locks[session]:
        # ---- bot 1
        b1 = (await ub.get_chat(bot1)).id
        q1 = _queues.setdefault((session, b1), asyncio.Queue())
        _drain(q1)
        await ub.send_message(b1, "/start")
        try:
            await _wait(q1, lambda m: True, 8)
        except asyncio.TimeoutError:
            pass
        await ub.send_message(b1, LINK_CMD)
        menu = await _wait(q1, lambda m: _button(m, MENU_BUTTON) is not None, 30)
        try:
            await menu.click(_button(menu, MENU_BUTTON))
        except TimeoutError:        # some bots answer the callback late/never; the click itself was sent
            pass
        try:
            await _wait(q1, lambda m: True, 5)   # e.g. "send me the file"
        except asyncio.TimeoutError:
            pass
        _drain(q1)
        try:
            await ub.get_chat(file_chat_id)      # makes sure the userbot knows the channel
        except Exception:
            pass
        await ub.copy_message(b1, file_chat_id, file_msg_id)
        r = await _wait(q1, lambda m: extract_link(m, "start=") is not None, timeout)
        link1 = extract_link(r, "start=")
        if not bot2:
            return link1, None

        # ---- bot 2
        b2 = (await ub.get_chat(bot2)).id
        q2 = _queues.setdefault((session, b2), asyncio.Queue())
        _drain(q2)
        await ub.send_message(b2, "/start")
        try:
            await _wait(q2, lambda m: True, 8)
        except asyncio.TimeoutError:
            pass
        _drain(q2)
        await ub.send_message(b2, link1)
        r2 = await _wait(q2, lambda m: extract_link(m) not in (None, link1), timeout)
        return link1, extract_link(r2)