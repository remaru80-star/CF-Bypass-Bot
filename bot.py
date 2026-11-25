import asyncio
import html
import io
import logging
import math
import os
import re
import shutil
import subprocess
import time
import uuid
from collections import OrderedDict, defaultdict
from concurrent.futures import ThreadPoolExecutor
from types import SimpleNamespace
from urllib.parse import quote_plus, urlparse

from motor.motor_asyncio import AsyncIOMotorClient
from pyrogram import Client, enums, filters, idle
from pyrogram.types import (BotCommand, BotCommandScopeChat, InlineKeyboardButton, InlineKeyboardMarkup,
                            InputMediaPhoto)

import catalog
import config
from downloader import fetch, fetch_bytes, fetch_image
import templating as T
from pipeline import QUALITY_CHOICES, Pipeline, chan_name
from userbot_links import (LoginError, drop_userbot, get_userbot, login_cancel, login_code, login_password,
                           login_start)
from scraper import SCRAPERS
from store import Store

try:
    from PIL import Image, ImageDraw, ImageFont
    PIL_OK = True
except Exception:  # poster grids are optional: without Pillow the list is text-only
    PIL_OK = False

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(name)s: %(message)s", datefmt="%H:%M:%S")
for noisy in ("pyrogram", "websocket"):
    logging.getLogger(noisy).setLevel(logging.WARNING)
os.makedirs(config.DOWNLOAD_DIR, exist_ok=True)

os.makedirs(config.SESSION_DIR, exist_ok=True)
app = Client(
    "cfdl",
    workdir=config.SESSION_DIR,
    api_id=config.API_ID,
    api_hash=config.API_HASH,
    bot_token=config.BOT_TOKEN,
)

HTML = enums.ParseMode.HTML
esc = html.escape
EPISODE_RE = re.compile(config.EPISODE_URL_PATTERN, re.I)
SERIES_RE = re.compile(config.SERIES_URL_PATTERN, re.I)
SITE_HOST = urlparse(config.SITE_URL).netloc.lower().removeprefix("www.")
VIDEO_EXT = (".mp4", ".mkv", ".webm", ".mov")
LINK_TTL = 20 * 60  # download links are only trusted for 20 minutes

# ---- admin pipeline (created in main())
DB = None
PIPE = None

# ---- concurrency state (created in main(), needs the running loop)
SLOTS: asyncio.Queue = None            # free browser slot ids
EXECUTORS: list = []                   # one single-thread executor per browser slot
TRANSFERS: asyncio.Semaphore = None    # simultaneous download+upload jobs
ACTIVE = defaultdict(int)              # user id -> running jobs
TASKS: set = set()                     # keep references to running job tasks
CACHE: dict = {}                       # (kind, url) -> (time, scrape result)
INFLIGHT: dict = {}                    # (kind, url) -> future shared by identical requests

SERIES: "OrderedDict[str, dict]" = OrderedDict()    # token -> series scrape result
EPISODES: "OrderedDict[str, dict]" = OrderedDict()  # token -> episode scrape result (links)
LISTINGS: "OrderedDict[str, dict]" = OrderedDict()  # token -> {res, posters, screen} for list pages
POSTER_CACHE: "OrderedDict[str, bytes]" = OrderedDict()  # poster url -> image bytes


def remember(store, key, val, limit=200):
    store[key] = val
    while len(store) > limit:
        store.popitem(last=False)


def site_url(path=""):
    return config.SITE_URL.rstrip("/") + "/" + path.lstrip("/")


def search_url(q):
    return site_url() + "?s=" + quote_plus(q)


MENU_ROWS = [
    [("🔍 Search", "m|search"), ("🆕 Latest", "m|latest")],
    [("📚 Series", "m|series"), ("📃 A–Z list", "m|list")],
    [("🔓 Uncensored", "m|unc"), ("🧊 3D", "m|3d")],
    [("🏷 Genres", "m|genres"), ("🏢 Studios", "m|studios")],
    [("🔥 Featured", "m|featured")],
]
MENU_PATHS = {"series": "hentai-series/", "list": "hentai-list/", "unc": "genre/uncensored/", "3d": "genre/3d/"}
MENU_TEXT = "🍥 <b>Hentaimama</b>\nPick a section, or just type a title to search."


def menu_keyboard():
    return InlineKeyboardMarkup([[InlineKeyboardButton(t, callback_data=d) for t, d in row] for row in MENU_ROWS])


def nav_row():
    return [InlineKeyboardButton("🏠 Menu", callback_data="m|home"),
            InlineKeyboardButton("🔍 Search", callback_data="m|search")]


def hum(n: float) -> str:
    for u in ("B", "KB", "MB", "GB"):
        if n < 1024:
            return f"{n:.1f}{u}"
        n /= 1024
    return f"{n:.1f}TB"


def clip(s, n):
    s = re.sub(r"\s+", " ", s or "").strip()
    return s if len(s) <= n else s[: n - 1].rstrip() + "…"


async def safe_edit(msg, text, **kw):
    try:
        await msg.edit_text(text, **kw)
    except Exception:
        pass


def _allowed(user_id) -> bool:
    return not config.AUTH_USERS or user_id in config.AUTH_USERS or user_id in config.ADMIN_IDS


is_auth = filters.create(lambda _, __, m: bool(m.from_user) and _allowed(m.from_user.id))

# /add_task and template editing are small step-by-step conversations, kept per admin
WIZ: dict = {}
TEXT_STEPS = ("link", "file", "episode", "sub", "tpl", "bot1", "bot2", "post", "ub_phone", "ub_code", "ub_pass",
              "bk_bot1", "bk_bot2", "bk_post")
in_wizard = filters.create(lambda _, __, m: bool(m.from_user) and WIZ.get(m.from_user.id, {}).get("step") in TEXT_STEPS)


# ------------------------------------------------------------------ captions / keyboards
def build_caption(title, genres, info, desc, tail="", series=None):
    head = [f"<b>{esc(clip(title, 200))}</b>"]
    if series:
        head.append(f"📺 {esc(clip(series, 120))}")
    if genres:
        head.append("🏷 " + esc(", ".join(genres[:8])))
    head += [esc(clip(i, 80)) for i in (info or [])[:6]]
    base = "\n".join(head)
    tail_s = f"\n\n{tail}" if tail else ""
    room = 900 - len(base) - len(tail_s)
    body = f"\n\n{esc(clip(desc, room))}" if desc and room > 60 else ""
    cap = base + body + tail_s
    return cap if len(cap) <= 1024 else base + tail_s


def ep_label(e, idx):
    return f"EP {e['n']}" if e.get("n") is not None else clip(e.get("label") or str(idx + 1), 14)


def episode_keyboard(token, eps, page=0):
    size = config.PAGE_SIZE
    start = page * size
    btns = [InlineKeyboardButton(ep_label(e, start + i), callback_data=f"e|{token}|{start + i}")
            for i, e in enumerate(eps[start:start + size])]
    rows = [btns[i:i + 5] for i in range(0, len(btns), 5)]
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅️ Prev", callback_data=f"p|{token}|{page - 1}"))
    if start + size < len(eps):
        nav.append(InlineKeyboardButton("Next ➡️", callback_data=f"p|{token}|{page + 1}"))
    if nav:
        rows.append(nav)
    rows.append(nav_row())
    return InlineKeyboardMarkup(rows)


def quality_keyboard(token, links):
    rows = [[InlineKeyboardButton(l["label"], callback_data=f"d|{token}|{i}") for i, l in enumerate(links)],
            [InlineKeyboardButton("All", callback_data=f"d|{token}|all")],
            nav_row()]
    return InlineKeyboardMarkup(rows)


async def get_image(info, url):
    """Download a thumbnail with the browser session; returns (path, dir) or (None, None)."""
    if not url:
        return None, None
    d = os.path.join(config.DOWNLOAD_DIR, "img_" + uuid.uuid4().hex[:8])
    try:
        path = await asyncio.get_running_loop().run_in_executor(None, fetch_image, info, url, d)
        return path, d
    except Exception as e:
        logging.warning("thumbnail failed: %s", e)
        shutil.rmtree(d, ignore_errors=True)
        return None, None


async def send_card(m, caption, img, kb=None):
    if img:
        try:
            return await m.reply_photo(img, caption=caption, parse_mode=HTML, reply_markup=kb)
        except Exception:
            logging.exception("photo send failed, falling back to text")
    return await m.reply_text(caption, parse_mode=HTML, reply_markup=kb)


# ------------------------------------------------------------------ video helpers
def video_meta(path: str, workdir: str):
    thumb, dur = None, 0
    try:
        out = subprocess.run(
            ["ffprobe", "-v", "error", "-show_entries", "format=duration",
             "-of", "default=nw=1:nk=1", path],
            capture_output=True, text=True, timeout=30,
        ).stdout.strip()
        dur = int(float(out)) if out else 0
        thumb = os.path.join(workdir, "thumb.jpg")
        subprocess.run(
            ["ffmpeg", "-y", "-ss", str(min(5, max(dur // 2, 0))), "-i", path,
             "-vframes", "1", "-vf", "scale=320:-1", thumb],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=60,
        )
        if not os.path.exists(thumb):
            thumb = None
    except Exception:
        pass
    return thumb, dur


async def up_progress(cur, total, st, box):
    now = time.time()
    if now - box[0] < 4:
        return
    box[0] = now
    await safe_edit(st, f"⬆️ Uploading {box[1]} {hum(cur)} / {hum(total)} ({cur * 100 // max(total, 1)}%)")


def pick(links, q):
    if q == "all":
        return links
    for l in links:
        if l["label"].lower() == q:
            return [l]
    return [links[0]]  # best (links are sorted best first)


async def download_upload(m, st, info, link):
    loop = asyncio.get_running_loop()
    label = link["label"]
    if TRANSFERS.locked():
        await safe_edit(st, f"⏳ {label}: waiting for a free download slot...")
    async with TRANSFERS:
        job_dir = os.path.join(config.DOWNLOAD_DIR, uuid.uuid4().hex[:8])
        try:
            state = {"done": 0, "total": 0, "name": ""}
            fut = loop.run_in_executor(None, fetch, dict(info, url=link["url"]), job_dir, state)
            while not fut.done():
                await asyncio.sleep(4)
                t = state["total"]
                pct = f" ({state['done'] * 100 // t}%)" if t else ""
                await safe_edit(st, f"⬇️ Downloading {label} {state['name']}\n{hum(state['done'])}"
                                    f"{' / ' + hum(t) if t else ''}{pct}")
            path = await fut

            if os.path.getsize(path) > config.MAX_SIZE:
                raise Exception(f"{label}: file is larger than 2 GB (Telegram bot limit)")

            box = [0.0, label]
            caption = f"{os.path.basename(path)}  [{label}]"
            if path.lower().endswith(VIDEO_EXT):
                thumb, dur = await loop.run_in_executor(None, video_meta, path, job_dir)
                await m.reply_video(
                    path, caption=caption, duration=dur, thumb=thumb,
                    supports_streaming=True, progress=up_progress, progress_args=(st, box),
                )
            else:
                await m.reply_document(
                    path, caption=caption, progress=up_progress, progress_args=(st, box),
                )
        finally:
            shutil.rmtree(job_dir, ignore_errors=True)


# ------------------------------------------------------------------ browser slots
def new_job():
    return {"t0": time.time(), "tag": uuid.uuid4().hex[:4], "step": "starting"}


async def run_scrape(st, job, data, icon="🔎"):
    """Take a free browser slot, run the scrape in that browser's own thread, give the slot back."""
    loop = asyncio.get_running_loop()
    job["step"] = "waiting for a free browser"
    getter = asyncio.ensure_future(SLOTS.get())
    try:
        while True:
            done, _ = await asyncio.wait({getter}, timeout=5)
            if done:
                break
            await safe_edit(st, f"⏳ All {config.BROWSER_WORKERS} browsers are busy, you're in line...")
    except BaseException:
        getter.cancel()
        raise
    slot = getter.result()
    job["t0"] = t0 = time.time()
    try:
        fut = loop.run_in_executor(EXECUTORS[slot], SCRAPERS[slot], dict(data, job=job))
        while True:
            try:
                return await asyncio.wait_for(asyncio.shield(fut), timeout=5)
            except asyncio.TimeoutError:
                el = int(time.time() - t0)
                if el > 240:
                    SCRAPERS[slot].close()  # kill the stuck Chrome; it restarts on the next job
                    EXECUTORS[slot] = ThreadPoolExecutor(max_workers=1)  # abandon the hung thread
                    raise Exception(f"Timed out at step: {job.get('step')}")
                await safe_edit(st, f"{icon} {job.get('step')} ({el}s)")
    finally:
        SLOTS.put_nowait(slot)


async def scrape_cached(kind, url, st, job, icon="🔎"):
    """Reuse a recent result for the same page; identical simultaneous requests share one browser run."""
    key = (kind, url)
    hit = CACHE.get(key)
    if hit and time.time() - hit[0] < config.CACHE_TTL:
        return hit[1]
    waiter = INFLIGHT.get(key)
    if waiter:
        await safe_edit(st, "⏳ Same page is already being opened for another request...")
        return await asyncio.shield(waiter)
    fut = asyncio.get_running_loop().create_future()
    INFLIGHT[key] = fut
    try:
        res = await run_scrape(st, job, {"kind": kind, "url": url}, icon)
        CACHE[key] = (time.time(), res)
        if len(CACHE) > 200:
            CACHE.pop(min(CACHE, key=lambda k: CACHE[k][0]), None)
        fut.set_result(res)
        return res
    except BaseException as e:
        fut.set_exception(e if isinstance(e, Exception) else Exception("cancelled"))
        fut.exception()  # mark as retrieved even when nobody else is waiting
        raise
    finally:
        INFLIGHT.pop(key, None)


async def report_error(m, st, e, job=None):
    logging.exception("job failed")
    text = f"🔎 {e}" if str(e).startswith("No results") else f"❌ Failed: {e}"
    if st:
        await safe_edit(st, text)
    else:
        await m.reply_text(text)
    shot = (job or {}).get("shot")
    if shot and os.path.exists(str(shot)):
        try:
            await m.reply_photo(str(shot), caption="What the browser saw")
        except Exception:
            pass
        job["shot"] = None


# ------------------------------------------------------------------ jobs
async def process_series(job_in):
    m, url = job_in["m"], job_in["url"]
    st = await m.reply_text("📚 Opening series page...", quote=True)
    job, img_dir = new_job(), None
    try:
        res = await scrape_cached("series", url, st, job, "📚")
        eps = res["episodes"]
        token = uuid.uuid4().hex[:8]
        remember(SERIES, token, res)
        img, img_dir = await get_image(res, res.get("image"))
        cap = build_caption(res["title"], res["genres"], res["info"], res["desc"],
                            tail=f"📚 {len(eps)} episodes — pick one:")
        await st.delete()
        await send_card(m, cap, img, episode_keyboard(token, eps, 0))
    except Exception as e:
        await report_error(m, st, e, job)
    finally:
        if img_dir:
            shutil.rmtree(img_dir, ignore_errors=True)


async def process_episode(job_in):
    m, url = job_in["m"], job_in["url"]
    st = await m.reply_text(f"🔎 Opening {job_in.get('label') or 'episode'}...", quote=True)
    job, img_dir = new_job(), None
    try:
        res = await scrape_cached("episode", url, st, job)
        links, meta = res["links"], res["meta"]
        token = uuid.uuid4().hex[:8]
        remember(EPISODES, token, dict(res, t=time.time()))

        ask = config.QUALITY == "ask" and len(links) > 1
        tail = "Pick a quality:" if ask else "Qualities: " + ", ".join(l["label"] for l in links)
        img, img_dir = await get_image(res, meta.get("image"))
        cap = build_caption(meta["title"] or job_in.get("label") or "Episode", meta["genres"], meta["info"],
                            meta["desc"], tail=tail, series=job_in.get("series_title"))
        await st.delete()
        await send_card(m, cap, img, quality_keyboard(token, links) if ask else None)

        if not ask:
            st2 = await m.reply_text("⬇️ Starting...")
            for l in pick(links, config.QUALITY if config.QUALITY != "ask" else "best"):
                await download_upload(m, st2, res, l)
            await st2.delete()
    except Exception as e:
        await report_error(m, st, e, job)
    finally:
        if img_dir:
            shutil.rmtree(img_dir, ignore_errors=True)


async def process_download(job_in):
    m = job_in["m"]
    entry = EPISODES.get(job_in["token"])
    if not entry or time.time() - entry["t"] > LINK_TTL:
        return await m.reply_text("Links expired. Open the episode again from the list.")
    links = entry["links"]
    chosen = links if job_in["sel"] == "all" else [links[int(job_in["sel"])]]
    st = await m.reply_text("⬇️ Starting...")
    try:
        for l in chosen:
            await download_upload(m, st, entry, l)
        await st.delete()
    except Exception as e:
        await report_error(m, st, e)


# ------------------------------------------------------------------ list pages (poster grid + numbered buttons)
class NullMsg:
    """Stand-in status message when we edit an existing card instead of sending a new one."""
    async def edit_text(self, *a, **k):
        pass


def classify(url):
    """episode | series | listing | None (not our site)."""
    if urlparse(url).netloc.lower().removeprefix("www.") != SITE_HOST:
        return None
    if EPISODE_RE.search(url):
        return "episode"
    if SERIES_RE.search(url):
        return "series"
    return "listing"


def page_url(res, n):
    tpl = res.get("tpl") or ""
    if tpl and 1 <= n <= res["pages"]:
        return re.sub(r"page/987654321/?(?=\?|$)", "", tpl) if n == 1 else tpl.replace("987654321", str(n))
    if n == res["page"] + 1:
        return res.get("next") or None
    if n == res["page"] - 1:
        return res.get("prev") or None
    return None


def per_screen(res):
    return 10 if res["flat"] else config.LISTING_PER_SCREEN


def n_screens(res):
    return max(1, math.ceil(len(res["items"]) / per_screen(res)))


def nice_heading(h):
    return re.sub(r"^Studios?/", "Studio: ", re.sub(r"^Genres?/", "Genre: ", h or ""))


def item_line(n, it):
    bits = []
    if it.get("badge"):
        bits.append(it["badge"])
    if it.get("rating"):
        bits.append(f"⭐{it['rating']}")
    tags = it.get("tags", [])
    eps = next((t for t in tags if "episode" in t.lower()), None)
    if eps:
        bits.append(eps.replace("Episodes", "eps").replace("Episode", "ep"))
    when = next((t for t in tags if re.fullmatch(r"\d{4}|\d{1,2}/\d{4}", t)), None)
    if when:
        bits.append(when)
    lang = next((t for t in tags if t.upper() in ("SUB", "DUB", "RAW", "UNCENSORED")), None)
    if lang:
        bits.append(lang)
    tail = " — " + " · ".join(bits) if bits else ""
    return f"{n}. <b>{esc(clip(it['title'], 40))}</b>{esc(tail)}"


def listing_view(token, res, screen):
    per, screens = per_screen(res), n_screens(res)
    screen = max(0, min(screen, screens - 1))
    lo = screen * per
    hi = min(len(res["items"]), lo + per)
    sub = [f"Page {res['page']}/{res['pages']}"] if res["pages"] > 1 else []
    sub.append(f"{lo + 1}–{hi} of {len(res['items'])}" + (" on this page" if res["pages"] > 1 else ""))
    lines = [f"📚 <b>{esc(clip(nice_heading(res['heading']), 80))}</b>", " · ".join(sub), ""]
    lines += [item_line(i - lo + 1, res["items"][i]) for i in range(lo, hi)]
    caption = "\n".join(lines) + "\n\nTap a number to open it."
    if len(caption) > 1024:  # very long titles: drop the extras
        caption = "\n".join(l.split(" — ")[0] for l in lines) + "\n\nTap a number to open it."
    btns = [InlineKeyboardButton(str(i - lo + 1), callback_data=f"l|{token}|{i}") for i in range(lo, hi)]
    rows = [btns[i:i + 4] for i in range(0, len(btns), 4)]
    rows.append([InlineKeyboardButton("⬅️", callback_data=f"g|{token}|p"),
                 InlineKeyboardButton(f"{screen + 1}/{screens}", callback_data=f"g|{token}|x"),
                 InlineKeyboardButton("➡️", callback_data=f"g|{token}|n")])
    if res["pages"] > 1:
        rows.append([InlineKeyboardButton("⏮ First page", callback_data=f"g|{token}|f"),
                     InlineKeyboardButton(f"Last ({res['pages']}) ⏭", callback_data=f"g|{token}|z")])
    elif screens > 12:  # long flat index: jump 10 screens at a time
        rows.append([InlineKeyboardButton("⏪ -10", callback_data=f"g|{token}|m"),
                     InlineKeyboardButton("+10 ⏩", callback_data=f"g|{token}|a")])
    rows.append(nav_row())
    return caption, InlineKeyboardMarkup(rows), lo, hi, screen


def make_collage(tiles, path):
    """tiles: list of image bytes (or None). Numbered poster grid, 4 per row."""
    W, H, G, cols = 190, 285, 8, 4
    rows = math.ceil(len(tiles) / cols)
    sheet = Image.new("RGB", (cols * W + (cols + 1) * G, rows * H + (rows + 1) * G), (20, 26, 36))
    d = ImageDraw.Draw(sheet)
    try:
        font = ImageFont.load_default(size=26)
    except TypeError:
        font = ImageFont.load_default()
    for i, raw in enumerate(tiles):
        x, y = G + (i % cols) * (W + G), G + (i // cols) * (H + G)
        tile = None
        if raw:
            try:
                im = Image.open(io.BytesIO(raw)).convert("RGB")
                r = max(W / im.width, H / im.height)
                im = im.resize((int(im.width * r) + 1, int(im.height * r) + 1))
                l, t = (im.width - W) // 2, (im.height - H) // 2
                tile = im.crop((l, t, l + W, t + H))
            except Exception:
                tile = None
        sheet.paste(tile or Image.new("RGB", (W, H), (45, 55, 72)), (x, y))
        d.ellipse((x + 6, y + 6, x + 46, y + 46), fill=(137, 76, 168))
        try:
            d.text((x + 26, y + 26), str(i + 1), fill="white", font=font, anchor="mm")
        except Exception:
            d.text((x + 20, y + 16), str(i + 1), fill="white", font=font)
    sheet.save(path, "JPEG", quality=85)


async def load_posters(res):
    """All posters of the page, downloaded in parallel (cached by URL)."""
    loop = asyncio.get_running_loop()

    async def one(it):
        u = it.get("poster")
        if not u:
            return None
        if u in POSTER_CACHE:
            return POSTER_CACHE[u]
        try:
            raw = await loop.run_in_executor(None, fetch_bytes, res, u)
        except Exception as e:
            logging.warning("poster failed: %s", e)
            return None
        remember(POSTER_CACHE, u, raw, 600)
        return raw

    return await asyncio.gather(*(one(it) for it in res["items"]))


async def render_listing(token, screen, edit_msg=None, reply_to=None):
    """Show one screen of a list: edit the existing card in place, or send a new one."""
    loop = asyncio.get_running_loop()
    st = LISTINGS[token]
    res = st["res"]
    caption, kb, lo, hi, screen = listing_view(token, res, screen)
    st["screen"] = screen
    img = None
    tiles = st["posters"][lo:hi]
    if PIL_OK and not res["flat"] and any(tiles):
        img = os.path.join(config.DOWNLOAD_DIR, f"lst_{uuid.uuid4().hex[:8]}.jpg")
        try:
            await loop.run_in_executor(None, make_collage, tiles, img)
        except Exception:
            logging.exception("collage failed, sending text only")
            img = None
    try:
        if edit_msg is not None:
            has_photo = bool(getattr(edit_msg, "photo", None))
            try:
                if img and has_photo:
                    await edit_msg.edit_media(InputMediaPhoto(img, caption=caption, parse_mode=HTML), reply_markup=kb)
                    return
                if not img and not has_photo:
                    await edit_msg.edit_text(caption, parse_mode=HTML, reply_markup=kb)
                    return
            except Exception as e:
                if "NOT_MODIFIED" in str(e).upper():
                    return
                logging.warning("edit failed, sending a new card: %s", e)
            reply_to = edit_msg  # type changed or edit failed: send fresh, drop the old card
        if img:
            await reply_to.reply_photo(img, caption=caption, parse_mode=HTML, reply_markup=kb)
        else:
            await reply_to.reply_text(caption, parse_mode=HTML, reply_markup=kb)
        if edit_msg is not None:
            try:
                await edit_msg.delete()
            except Exception:
                pass
    finally:
        if img:
            try:
                os.remove(img)
            except OSError:
                pass


async def present_listing(m, res, screen=0, edit=None):
    """Poster grid for a list result (list page, search results, home sections)."""
    posters = [None] * len(res["items"])
    if PIL_OK and not res["flat"]:
        posters = await load_posters(res)
    token = uuid.uuid4().hex[:8]
    remember(LISTINGS, token, {"res": res, "posters": posters, "screen": 0})
    s = n_screens(res) - 1 if screen == "last" else int(screen or 0)
    await render_listing(token, s, edit_msg=edit, reply_to=m)


async def process_listing(job_in):
    m, url, edit = job_in["m"], job_in["url"], job_in.get("edit")
    st = None if edit else await m.reply_text("📚 Loading list...", quote=True)
    job = new_job()
    try:
        res = await scrape_cached("listing", url, st or NullMsg(), job, "📚")
        await present_listing(m, res, job_in.get("screen", 0), edit)
        if st:
            await st.delete()
    except Exception as e:
        await report_error(m, st, e, job)


async def process_home(job_in):
    m, which = job_in["m"], job_in["which"]
    st = await m.reply_text("🏠 Loading...", quote=True)
    job = new_job()
    try:
        data = await scrape_cached("home", config.SITE_URL, st, job, "🏠")
        res = data[which]
        if not res["items"]:
            raise Exception("Nothing to show there right now.")
        await present_listing(m, res)
        await st.delete()
    except Exception as e:
        await report_error(m, st, e, job)


# ------------------------------------------------------------------ genre / studio pickers (no browser needed)
def catalog_view(kind, page):
    items = catalog.GENRES if kind == "g" else catalog.STUDIOS
    size = 24
    pages = max(1, -(-len(items) // size))
    page = max(0, min(page, pages - 1))
    chunk = items[page * size:(page + 1) * size]
    btns = [InlineKeyboardButton(clip(name, 18), callback_data=f"o|{kind}|{page * size + i}")
            for i, (name, _) in enumerate(chunk)]
    rows = [btns[i:i + 3] for i in range(0, len(btns), 3)]
    rows.append([InlineKeyboardButton("⬅️", callback_data=f"c|{kind}|{page - 1}"),
                 InlineKeyboardButton(f"{page + 1}/{pages}", callback_data=f"c|{kind}|{page}"),
                 InlineKeyboardButton("➡️", callback_data=f"c|{kind}|{page + 1}")])
    rows.append([InlineKeyboardButton("🏠 Menu", callback_data="m|back")])
    title = "🏷 <b>Genres</b>" if kind == "g" else "🏢 <b>Studios</b>"
    return f"{title} — {len(items)} · page {page + 1}/{pages}\nTap one to browse it.", InlineKeyboardMarkup(rows)


async def do_search(m, text):
    q = re.sub(r"\s+", " ", text or "").strip()[:80]
    if len(q) < 2:
        return await m.reply_text("Type at least 2 letters to search.")
    spawn({"type": "listing", "m": m, "url": search_url(q), "uid": m.from_user.id, "screen": 0})


HANDLERS = {"series": process_series, "episode": process_episode, "download": process_download,
            "listing": process_listing, "home": process_home}


async def guarded(job_in):
    """Per-user cap, so one person can't take every browser/transfer slot."""
    uid = job_in["uid"]
    if ACTIVE[uid] >= config.MAX_JOBS_PER_USER:
        try:
            await job_in["m"].reply_text(f"⏳ You already have {ACTIVE[uid]} jobs running. Wait for one to finish.")
        except Exception:
            pass
        return
    ACTIVE[uid] += 1
    try:
        await HANDLERS[job_in["type"]](job_in)
    except Exception:
        logging.exception("job crashed")
    finally:
        ACTIVE[uid] -= 1


def spawn(job_in):
    """Every request runs as its own task, so users never wait behind each other's chat handling."""
    t = asyncio.create_task(guarded(job_in))
    TASKS.add(t)
    t.add_done_callback(TASKS.discard)


# ------------------------------------------------------------------ telegram handlers
@app.on_message(filters.command(["start", "menu", "home"]) & filters.private & is_auth)
async def start(_, m):
    await m.reply_text(MENU_TEXT + "\n\nYou can also send a link (list, series or episode page).\n"
                       "/help lists every command. /status shows the load.",
                       parse_mode=HTML, reply_markup=menu_keyboard())
    if m.from_user.id in config.ADMIN_IDS:
        await register_commands(m.from_user.id)  # makes the admin commands show up in this admin's menu


@app.on_message(filters.command("search") & filters.private & is_auth)
async def search_cmd(_, m):
    q = " ".join(m.command[1:])
    if not q.strip():
        return await m.reply_text("Send /search followed by a title, or just type the title.")
    await do_search(m, q)


@app.on_message(filters.command("status") & filters.private & is_auth)
async def status(_, m):
    busy = config.BROWSER_WORKERS - SLOTS.qsize()
    await m.reply_text(
        f"Browsers: {busy}/{config.BROWSER_WORKERS} busy\n"
        f"Downloads/uploads: {config.MAX_TRANSFERS - TRANSFERS._value}/{config.MAX_TRANSFERS} running\n"
        f"Your active jobs: {ACTIVE[m.from_user.id]}/{config.MAX_JOBS_PER_USER}"
    )


@app.on_message(filters.command("browse") & filters.private & is_auth)
async def browse(_, m):
    url = config.SITE_URL.rstrip("/") + "/" + config.BROWSE_PATH.lstrip("/")
    spawn({"type": "listing", "m": m, "url": url, "uid": m.from_user.id, "screen": 0})


@app.on_message(filters.private & filters.text & ~filters.regex(r"^https?://") & ~filters.regex(r"^/") & ~in_wizard & is_auth)
async def on_text(_, m):
    await do_search(m, m.text)  # plain text = search


@app.on_message(filters.private & filters.regex(r"^https?://\S+") & ~in_wizard & is_auth)
async def on_link(_, m):
    url = m.text.strip().split()[0]
    kind = classify(url)
    if not kind:
        return await m.reply_text(f"I only handle links from {SITE_HOST}.")
    spawn({"type": kind, "m": m, "url": url, "uid": m.from_user.id, "screen": 0})


@app.on_callback_query(filters.regex(r"^[epdglmco]\|"))
async def on_button(_, cq):
    if not _allowed(cq.from_user.id):
        return await cq.answer("Not allowed", show_alert=True)
    parts = cq.data.split("|")
    kind, token = parts[0], parts[1]
    arg = parts[2] if len(parts) > 2 else ""
    uid = cq.from_user.id

    if kind == "m":  # main menu
        if token == "search":
            await cq.answer()
            return await cq.message.reply_text("🔍 Type the title you want to find (at least 2 letters).")
        if token == "home":
            await cq.answer()
            return await cq.message.reply_text(MENU_TEXT, parse_mode=HTML, reply_markup=menu_keyboard())
        if token == "back":
            await safe_edit(cq.message, MENU_TEXT, parse_mode=HTML, reply_markup=menu_keyboard())
            return await cq.answer()
        if token in ("genres", "studios"):
            text, kb = catalog_view("g" if token == "genres" else "s", 0)
            await safe_edit(cq.message, text, parse_mode=HTML, reply_markup=kb)
            return await cq.answer()
        if token in ("latest", "featured"):
            spawn({"type": "home", "m": cq.message, "which": token, "uid": uid})
            return await cq.answer("Loading...")
        if token in MENU_PATHS:
            spawn({"type": "listing", "m": cq.message, "url": site_url(MENU_PATHS[token]), "uid": uid, "screen": 0})
            return await cq.answer("Loading...")
        return await cq.answer()

    if kind == "c":  # genre / studio picker page
        text, kb = catalog_view(token, int(arg))
        await safe_edit(cq.message, text, parse_mode=HTML, reply_markup=kb)
        return await cq.answer()

    if kind == "o":  # genre / studio picked
        items = catalog.GENRES if token == "g" else catalog.STUDIOS
        name, slug = items[int(arg)]
        path = ("genre/" if token == "g" else "studio/") + slug + "/"
        spawn({"type": "listing", "m": cq.message, "url": site_url(path), "uid": uid, "screen": 0})
        return await cq.answer(f"Opening {clip(name, 30)}...")

    if kind == "p":  # episode list page
        res = SERIES.get(token)
        if not res:
            return await cq.answer("Expired, send the link again", show_alert=True)
        try:
            await cq.message.edit_reply_markup(episode_keyboard(token, res["episodes"], int(arg)))
        except Exception:
            pass
        return await cq.answer()

    if kind == "e":  # episode picked
        res = SERIES.get(token)
        if not res:
            return await cq.answer("Expired, send the link again", show_alert=True)
        ep = res["episodes"][int(arg)]
        spawn({"type": "episode", "m": cq.message, "url": ep["url"], "uid": uid,
               "label": ep_label(ep, int(arg)), "series_title": res["title"]})
        return await cq.answer(f"Opening {ep_label(ep, int(arg))}...")

    if kind == "l":  # item picked from a list: a series page or an episode page
        st = LISTINGS.get(token)
        if not st:
            return await cq.answer("Expired, send the link again", show_alert=True)
        it = st["res"]["items"][int(arg)]
        if classify(it["url"]) == "episode":
            spawn({"type": "episode", "m": cq.message, "url": it["url"], "uid": uid, "label": clip(it["title"], 30)})
        else:
            spawn({"type": "series", "m": cq.message, "url": it["url"], "uid": uid})
        return await cq.answer(f"Opening {clip(it['title'], 40)}...")

    if kind == "g":  # list navigation
        st = LISTINGS.get(token)
        if not st:
            return await cq.answer("Expired, send the link again", show_alert=True)
        res, cur = st["res"], st["screen"]
        screens = n_screens(res)

        def load(n, screen=0):  # another site page: scrape it, then edit this card
            url = page_url(res, n)
            if not url:
                return False
            spawn({"type": "listing", "m": cq.message, "url": url, "uid": uid, "screen": screen, "edit": cq.message})
            return True

        if arg == "x":
            return await cq.answer(f"Screen {cur + 1}/{screens}")
        if arg in ("n", "a"):
            step = 10 if arg == "a" else 1
            if cur + step < screens or (arg == "a" and cur < screens - 1):
                await render_listing(token, min(cur + step, screens - 1), edit_msg=cq.message)
                return await cq.answer()
            if arg == "n" and res["page"] < res["pages"] and load(res["page"] + 1):
                return await cq.answer(f"Loading page {res['page'] + 1}...")
            return await cq.answer("That's the end of the list")
        if arg in ("p", "m"):
            step = 10 if arg == "m" else 1
            if cur - step >= 0 or (arg == "m" and cur > 0):
                await render_listing(token, max(cur - step, 0), edit_msg=cq.message)
                return await cq.answer()
            if arg == "p" and res["page"] > 1 and load(res["page"] - 1, "last"):
                return await cq.answer(f"Loading page {res['page'] - 1}...")
            return await cq.answer("That's the start of the list")
        if arg == "f":
            if res["page"] > 1 and load(1):
                return await cq.answer("Loading page 1...")
            await render_listing(token, 0, edit_msg=cq.message)
            return await cq.answer()
        if arg == "z":
            if res["page"] < res["pages"] and load(res["pages"]):
                return await cq.answer(f"Loading page {res['pages']}...")
            await render_listing(token, screens - 1, edit_msg=cq.message)
            return await cq.answer()

    if kind == "d":  # quality picked
        if token not in EPISODES:
            return await cq.answer("Expired, open the episode again", show_alert=True)
        spawn({"type": "download", "m": cq.message, "token": token, "sel": arg, "uid": uid})
        return await cq.answer("Queued")


# ------------------------------------------------------------------ commands menu + /help
USER_COMMANDS = [
    ("start", "Open the main menu"),
    ("search", "Search by title: /search <title>"),
    ("browse", "Browse all series"),
    ("status", "Show the bot load"),
    ("help", "Show all commands"),
]
ADMIN_COMMANDS = [
    ("add_task", "Create an automation task (download + post)"),
    ("tasks", "List tasks: pause, resume, retry, delete"),
    ("templates", "Show the post templates and variables"),
    ("set_sub_template", "Edit the anime post (sub channel) template"),
    ("set_episode_template", "Edit the episode post template"),
    ("set_file_template", "Edit the file caption template"),
    ("reset_templates", "Restore the default templates"),
    ("userbot", "Log in the userbot account (phone number) / show it"),
    ("userbot_logout", "Remove the logged-in userbot account"),
    ("cancel", "Cancel the current add_task / template edit / login"),
]
ADMIN_NAMES = [c for c, _ in ADMIN_COMMANDS]
is_admin = filters.create(lambda _, __, m: bool(m.from_user) and m.from_user.id in config.ADMIN_IDS)
RAW = enums.ParseMode.DISABLED


def variables_text():
    return "\n".join(f"{{{k}}} — {v}" for k, v in T.VARIABLES.items())


def help_text(admin):
    lines = ["📖 <b>Help</b>", "Send a link, or just type a title to search.", "", "<b>Commands</b>"]
    lines += [f"/{c} — {esc(d)}" for c, d in USER_COMMANDS]
    if admin:
        lines += ["", "🔐 <b>Admin: automation pipeline</b>"]
        lines += [f"/{c} — {esc(d)}" for c, d in ADMIN_COMMANDS]
        lines += ["", "<b>How a task works</b>",
                  "Make me an admin of your 3 channels (permission to post messages), then send /add_task and answer: "
                  "Link · Download (All) · Technique · Quality · File channel · Episode channel · Sub channel.",
                  "• <b>Data Collect</b>: read all the data first, then download + post each episode.",
                  "• <b>One by one</b>: read, download and post one anime, then the next.",
                  "• <b>File channel</b>: the video files, with a full caption.",
                  "• <b>Episode channel</b>: one post per episode, with a Download button to the file.",
                  "• <b>Sub channel</b>: one post per anime, with episode-number buttons to the episode posts.",
                  "Channels can be given as -100…, @username, https://t.me/name or an invite link.",
                  "", "<b>Templates</b> (/templates, /set_sub_template …)",
                  "&lt;text&gt; = bold · &lt;q&gt;text&lt;/q&gt; = quote · [label](https://link) = link",
                  "Variables: " + esc(", ".join("{" + k + "}" for k in T.VARIABLES))]
    return "\n".join(lines)


async def register_commands(admin_id=None):
    """Default menu for everyone; the full menu (with admin commands) only for the admins."""
    try:
        if admin_id is None:
            await app.set_bot_commands([BotCommand(c, d) for c, d in USER_COMMANDS])
        for aid in ([admin_id] if admin_id else sorted(config.ADMIN_IDS)):
            try:
                await app.set_bot_commands([BotCommand(c, d) for c, d in USER_COMMANDS + ADMIN_COMMANDS],
                                           scope=BotCommandScopeChat(chat_id=aid))
            except Exception as e:  # the admin has not started the bot yet
                logging.info("admin menu for %s not set yet (%s); it is set when they send /start", aid, e)
    except Exception as e:
        logging.warning("could not set the commands menu: %s", e)


@app.on_message(filters.command("help") & filters.private & is_auth)
async def help_cmd(_, m):
    await m.reply_text(help_text(m.from_user.id in config.ADMIN_IDS), parse_mode=HTML)


async def pipe_ready(m):
    if PIPE is None:
        await m.reply_text("⚠️ The database is not connected. Set MONGO_URI in the .env file and restart the bot.")
        return False
    return True


# ------------------------------------------------------------------ /add_task wizard
CH_HELP = ("Send it as <code>-1001234567890</code>, <code>@username</code>, <code>https://t.me/name</code> or an "
           "invite link <code>https://t.me/+abc…</code>.\nMake me an <b>admin</b> there first (allowed to post messages).")
STEP_TEXT = {
    "link": "🔗 <b>Link</b>\nSend the link to work on: a list page (all its pages), one series page, or one episode page.\n"
            "Example: https://hentaimama.io/hentai-series/",
    "file": "📁 <b>File channel</b> — the video files are saved here.\n" + CH_HELP,
    "episode": "🎞 <b>Episode channel</b> — one post per episode, with a Download button.\n" + CH_HELP,
    "sub": "📚 <b>Sub channel</b> — one post per anime, with episode-number buttons.\n" + CH_HELP,
    "post": "📣 <b>Post channel</b> — same post as the episode post, but the button is the generated link.\n" + CH_HELP,
    "bot1": "🤖 <b>Link bot 1</b> — send its @username (the bot with /univarsal_link).",
}
STEP_ORDER = ["link", "download", "technique", "quality", "file", "episode", "sub", "confirm"]


def kb_rows(rows):
    return InlineKeyboardMarkup([[InlineKeyboardButton(t, callback_data=d) for t, d in row] for row in rows])


async def wizard_ask(target, step):
    """Send the question for a step (buttons for the choice steps, plain text for the others)."""
    if step in STEP_TEXT:
        return await target.reply_text(STEP_TEXT[step] + "\n\n/cancel to stop.", parse_mode=HTML)
    if step == "links":
        return await target.reply_text("🔗 <b>Link generation</b> (optional)\nA userbot gets links for each file from your link bots "
                                       "and posts in a post channel.", parse_mode=HTML,
                                       reply_markup=kb_rows([[("✅ Set up", "wz|ln|yes"), ("⏭ Skip", "wz|ln|no")]]))
    if step == "bot2":
        return await target.reply_text("🤖 <b>Link bot 2</b> — send its @username (it turns bot 1's link into the final link).",
                                       parse_mode=HTML, reply_markup=kb_rows([[("⏭ No bot 2", "wz|b2|skip")]]))
    if step == "confirm":
        return await target.reply_text(wizard_summary(w_data(target)), parse_mode=HTML,
                                       reply_markup=kb_rows([[("✅ Start the task", "wz|go"), ("❌ Cancel", "wz|cancel")]]))
    if step == "download":
        return await target.reply_text("⬇️ <b>Download</b>", parse_mode=HTML,
                                       reply_markup=kb_rows([[("✅ All", "wz|dl|all"), ("Custom (off for now)", "wz|dl|custom")]]))
    if step == "technique":
        return await target.reply_text(
            "⚙️ <b>Technique</b>\n🗂 <b>Data Collect</b> — read all the data first, then download + post each episode.\n"
            "➡️ <b>One by one</b> — read, download and post one anime, then the next anime.",
            parse_mode=HTML, reply_markup=kb_rows([[("🗂 Data Collect", "wz|tech|collect"), ("➡️ One by one", "wz|tech|onebyone")]]))
    if step == "quality":
        return await target.reply_text("🎚 <b>Quality</b>", parse_mode=HTML, reply_markup=kb_rows(
            [[("All", "wz|q|all"), ("1080p", "wz|q|1080p")], [("720p", "wz|q|720p"), ("480p", "wz|q|480p")]]))
    return None


def w_data(target):
    return WIZ[target.chat.id]["data"]


def wizard_summary(d):
    tech = "Data Collect" if d["technique"] == "collect" else "One by one"
    return ("📝 <b>Check the task</b>\n"
            f"🔗 {esc(d['link'])} ({d['kind']})\n⬇️ Download: All · ⚙️ {tech} · 🎚 {d['quality']}\n"
            f"📁 File: {esc(chan_name(d['file']))}\n🎞 Episode: {esc(chan_name(d['episode']))}\n"
            f"📚 Sub: {esc(chan_name(d['sub']))}"
            + (f"\n👤 Userbot: set · 🤖 {esc(d['link_bot1'])}" + (f" → {esc(d['link_bot2'])}" if d.get("link_bot2") else "")
               + f"\n📣 Post: {esc(chan_name(d['post']))}" if d.get("link_bot1") else ""))


async def resolve_channel(text):
    t = text.strip()
    m = re.match(r"^(?:https?://)?t\.me/c/(\d+)", t)
    if m:
        ident = int("-100" + m.group(1))
    elif re.fullmatch(r"-?\d{5,}", t):
        ident = int(t)
    elif re.match(r"^(?:https?://)?t\.me/(?:\+|joinchat/)", t):
        ident = t if t.startswith("http") else "https://" + t
    elif re.match(r"^(?:https?://)?t\.me/[A-Za-z0-9_]{4,}", t):
        ident = re.match(r"^(?:https?://)?t\.me/([A-Za-z0-9_]{4,})", t).group(1)
    else:
        ident = t.lstrip("@")
    return await app.get_chat(ident)


async def check_channel(chat):
    """The bot must be an admin that can post. Returns (channel dict, None) or (None, error text)."""
    name = esc(getattr(chat, "title", None) or str(chat.id))
    try:
        me = await app.get_chat_member(chat.id, "me")
    except Exception as e:
        return None, f"❌ I can't see <b>{name}</b> ({esc(str(e))}).\nAdd me to that channel as an admin first."
    can_post = getattr(getattr(me, "privileges", None), "can_post_messages", True)
    if me.status not in (enums.ChatMemberStatus.ADMINISTRATOR, enums.ChatMemberStatus.OWNER) or can_post is False:
        return None, f"❌ I'm not an admin with permission to post in <b>{name}</b>. Make me an admin, then send it again."
    return {"id": chat.id, "title": getattr(chat, "title", None), "username": getattr(chat, "username", None)}, None


@app.on_message(filters.command("add_task") & filters.private & is_admin)
async def add_task_cmd(_, m):
    if not await pipe_ready(m):
        return
    WIZ[m.from_user.id] = {"step": "link", "data": {}}
    await wizard_ask(m, "link")


@app.on_message(filters.command("cancel") & filters.private & is_admin)
async def cancel_cmd(_, m):
    await login_cancel(m.from_user.id)
    await m.reply_text("Cancelled. 👍" if WIZ.pop(m.from_user.id, None) else "Nothing to cancel.")


# ---- userbot account login: phone -> code -> (2FA password); the session is kept in MongoDB and shared by all tasks
@app.on_message(filters.command("userbot") & filters.private & is_admin)
async def userbot_cmd(_, m):
    if not await pipe_ready(m):
        return
    ub = await DB.userbot()
    new = len(m.command) > 1 and m.command[1].lower() == "new"
    if ub and not new:
        return await m.reply_text(f"👤 Userbot: <b>{esc(ub.get('name') or '')}</b> (id {ub.get('id')})\n"
                                  "Log in another account: /userbot new · remove: /userbot_logout", parse_mode=HTML)
    WIZ[m.from_user.id] = {"step": "ub_phone", "data": {}}
    await m.reply_text("📱 <b>Userbot login</b>\nSend the account's phone number with country code, e.g. <code>+919876543210</code>.\n"
                       "Use a spare account, not your main one. /cancel to stop.", parse_mode=HTML)


@app.on_message(filters.command("userbot_logout") & filters.private & is_admin)
async def userbot_logout_cmd(_, m):
    if not await pipe_ready(m):
        return
    ub = await DB.userbot()
    if not ub:
        return await m.reply_text("No userbot is logged in.")
    await drop_userbot(ub["session"])
    await DB.clear_userbot()
    await m.reply_text("✅ Userbot removed. Tasks with link generation will fail until you log in again with /userbot.")


async def userbot_login_step(m, w, step, text):
    uid = m.from_user.id
    try:
        await m.delete()  # phone / code / password should not stay in the chat
    except Exception:
        pass
    try:
        if step == "ub_phone":
            await login_start(uid, re.sub(r"[^\d+]", "", text), config.API_ID, config.API_HASH)
            w["step"] = "ub_code"
            return await m.reply_text("📲 Telegram sent a code to that account. Send it with spaces or dashes between the digits "
                                      "(like <code>1 2 3 4 5</code>) — Telegram cancels codes typed as plain digits.", parse_mode=HTML)
        if step == "ub_code":
            res = await login_code(uid, re.sub(r"\D", "", text))
        else:
            res = await login_password(uid, text)
    except LoginError as e:
        if not e.retry:
            WIZ.pop(uid, None)
        return await m.reply_text(f"❌ {esc(str(e))}" + (" Send it again." if e.retry else " Start again with /userbot."), parse_mode=HTML)
    if res[0] == "password":
        w["step"] = "ub_pass"
        return await m.reply_text("🔐 This account has two-step verification. Send its password.")
    session, me = res[1], res[2]
    old = await DB.userbot()
    if old:
        await drop_userbot(old["session"])
    await DB.set_userbot(session, me.first_name or "", me.id)
    WIZ.pop(uid, None)
    await m.reply_text(f"✅ Userbot logged in: <b>{esc(me.first_name or '')}</b> (id {me.id}).\n"
                       "Add it to your file channel, then use /add_task → Link generation.", parse_mode=HTML)


@app.on_message(filters.private & filters.text & ~filters.regex(r"^/") & is_admin & in_wizard)
async def wizard_text(_, m):
    uid, text = m.from_user.id, m.text.strip()
    w = WIZ[uid]
    step, d = w["step"], w.setdefault("data", {})

    if step == "tpl":
        return await save_template(m, w["name"], m.text)

    if step == "link":
        url = text.split()[0]
        kind = classify(url) if url.startswith("http") else None
        if not kind:
            return await m.reply_text(f"❌ I only handle links from {SITE_HOST}. Send the link again.")
        if urlparse(url).path.strip("/") == "" and not urlparse(url).query:
            url, kind = site_url(config.PIPELINE_SOURCE), "listing"  # the site's home = every series
            await m.reply_text(f"ℹ️ That's the home page, so I'll take every series from {url}")
        d["link"], d["kind"] = url, kind
        w["step"] = "download"
        return await wizard_ask(m, "download")

    if step in ("ub_phone", "ub_code", "ub_pass"):
        return await userbot_login_step(m, w, step, text)

    if step in ("bk_bot1", "bk_bot2"):
        uname = text.lstrip("@").split("/")[-1]
        try:
            ub = await get_userbot((await DB.userbot())["session"], config.API_ID, config.API_HASH)
            await ub.get_chat(uname)
        except Exception as e:
            return await m.reply_text(f"❌ The userbot can't find @{esc(uname)} ({esc(str(e)[:150])}). Send it again.", parse_mode=HTML)
        d["link_bot1" if step == "bk_bot1" else "link_bot2"] = uname
        w["step"] = "bk_bot2" if step == "bk_bot1" else "bk_post"
        await m.reply_text(f"✅ {step.replace('bk_bot', 'Link bot ')}: @{esc(uname)}", parse_mode=HTML)
        return await bulk_ask(m, w["step"])

    if step == "bk_post":
        try:
            chat = await resolve_channel(text)
        except Exception as e:
            return await m.reply_text(f"❌ I can't find that channel ({esc(str(e))}). Make me an admin there and send it again.",
                                      parse_mode=HTML)
        ch, err = await check_channel(chat)
        if err:
            return await m.reply_text(err, parse_mode=HTML)
        await DB.set_task(d["tid"], link_bot1=d["link_bot1"], link_bot2=d.get("link_bot2"), post_channel=ch)
        w["step"] = "bk_first"
        await m.reply_text(f"✅ Post channel: {esc(chan_name(ch))}\nLink generation is now also ON for this task's remaining episodes.",
                           parse_mode=HTML)
        return await bulk_ask(m, "bk_first")

    if step in ("bot1", "bot2"):
        uname = text.lstrip("@").split("/")[-1]
        try:
            ub = await get_userbot((await DB.userbot())["session"], config.API_ID, config.API_HASH)
            chat = await ub.get_chat(uname)
        except Exception as e:
            return await m.reply_text(f"❌ The userbot can't find @{esc(uname)} ({esc(str(e)[:150])}). Send it again.", parse_mode=HTML)
        d["link_bot1" if step == "bot1" else "link_bot2"] = uname
        w["step"] = "bot2" if step == "bot1" else "post"
        await m.reply_text(f"✅ {step.replace('bot', 'Link bot ')}: @{esc(uname)}", parse_mode=HTML)
        return await wizard_ask(m, w["step"])

    if step in ("file", "episode", "sub", "post"):
        try:
            chat = await resolve_channel(text)
        except Exception as e:
            return await m.reply_text(f"❌ I can't find that channel ({esc(str(e))}).\nMake me an admin there, then send it "
                                      "again (an @username or link works best).", parse_mode=HTML)
        ch, err = await check_channel(chat)
        if err:
            return await m.reply_text(err, parse_mode=HTML)
        d[step] = ch
        nxt = {"file": "episode", "episode": "sub", "sub": "links", "post": "confirm"}[step]
        w["step"] = nxt
        await m.reply_text(f"✅ {step.capitalize()} channel: {esc(chan_name(ch))}", parse_mode=HTML)
        if nxt == "confirm":
            return await m.reply_text(wizard_summary(d), parse_mode=HTML,
                                      reply_markup=kb_rows([[("✅ Start the task", "wz|go"), ("❌ Cancel", "wz|cancel")]]))
        return await wizard_ask(m, nxt)


@app.on_callback_query(filters.regex(r"^wz\|"))
async def on_wizard(_, cq):
    uid = cq.from_user.id
    if uid not in config.ADMIN_IDS:
        return await cq.answer("Admin only", show_alert=True)
    w = WIZ.get(uid)
    parts = cq.data.split("|")
    act, arg = parts[1], (parts[2] if len(parts) > 2 else "")
    if not w:
        return await cq.answer("This setup expired. Send /add_task again.", show_alert=True)
    d = w["data"]
    if act == "cancel":
        WIZ.pop(uid, None)
        await safe_edit(cq.message, "❌ Cancelled.")
        return await cq.answer()
    if act == "dl":
        if arg == "custom":
            return await cq.answer("Custom download is not available yet.", show_alert=True)
        d["download"], w["step"] = "all", "technique"
        await safe_edit(cq.message, "⬇️ Download: <b>All</b>", parse_mode=HTML)
    elif act == "tech":
        d["technique"], w["step"] = arg, "quality"
        await safe_edit(cq.message, "⚙️ Technique: <b>" + ("Data Collect" if arg == "collect" else "One by one") + "</b>", parse_mode=HTML)
    elif act == "q":
        d["quality"], w["step"] = arg, "file"
        await safe_edit(cq.message, f"🎚 Quality: <b>{esc(arg)}</b>", parse_mode=HTML)
    elif act == "ln":
        if arg == "yes":
            ub = await DB.userbot()
            if not ub:
                return await cq.answer("No userbot is logged in yet. Send /userbot, log in, then press Set up again.", show_alert=True)
            w["step"] = "bot1"
            await safe_edit(cq.message, f"🔗 Link generation: <b>set up</b>\n👤 Userbot: {esc(ub.get('name') or '')} (id {ub.get('id')})",
                            parse_mode=HTML)
        else:
            w["step"] = "confirm"
            await safe_edit(cq.message, "🔗 Link generation: <b>skipped</b>", parse_mode=HTML)
    elif act == "b2":
        d["link_bot2"], w["step"] = None, "post"
        await safe_edit(cq.message, "🤖 Link bot 2: <b>none</b>", parse_mode=HTML)
    elif act == "go":
        if w["step"] != "confirm":
            return await cq.answer("Finish the questions first.", show_alert=True)
        tid = await PIPE.add_task({"admin_id": uid, "link": d["link"], "kind": d["kind"], "download": d["download"],
                                   "technique": d["technique"], "quality": d["quality"], "file_channel": d["file"],
                                   "episode_channel": d["episode"], "sub_channel": d["sub"],
                                   **({"link_bot1": d["link_bot1"],
                                       "link_bot2": d.get("link_bot2"), "post_channel": d["post"]}
                                      if d.get("link_bot1") else {})})
        WIZ.pop(uid, None)
        await safe_edit(cq.message, f"✅ <b>Task #{tid} started.</b>\n/tasks shows the progress.", parse_mode=HTML)
        return await cq.answer("Started")
    await cq.answer()
    await wizard_ask(cq.message, w["step"])


# ------------------------------------------------------------------ tasks panel
STATUS_ICON = {"running": "▶️", "paused": "⏸", "done": "✅"}


async def tasks_view():
    tasks = await DB.all_tasks()
    if not tasks:
        return "No tasks yet. Create one with /add_task.", None
    lines, rows = ["📋 <b>Tasks</b>"], []
    for t in tasks:
        c = await DB.counts(t["_id"])
        eps = c["episodes"]
        lines.append(f"#{t['_id']} {STATUS_ICON.get(t['status'], '•')} {esc(clip(t['link'], 45))} — "
                     f"{eps['done']}/{sum(eps.values())} episodes")
        rows.append([InlineKeyboardButton(f"#{t['_id']} {STATUS_ICON.get(t['status'], '•')} {clip(t['link'].split('//')[-1], 28)}",
                                          callback_data=f"tk|open|{t['_id']}")])
    return "\n".join(lines), InlineKeyboardMarkup(rows)


async def task_view(tid):
    t = await DB.task(tid)
    if not t:
        return "That task no longer exists.", kb_rows([[("⬅️ Back", "tk|list|0")]])
    top = [("⏸ Pause", f"tk|pause|{tid}")] if t["status"] == "running" else (
        [("▶️ Resume", f"tk|resume|{tid}")] if t["status"] == "paused" else [])
    rows = ([top] if top else []) + [[("🔁 Retry failed", f"tk|retry|{tid}"), ("🔄 Refresh", f"tk|open|{tid}")],
                                     [("🔗 Bulk links (old files)", f"tk|bulk|{tid}")],
                                     [("🗑 Delete", f"tk|del|{tid}"), ("⬅️ Back", "tk|list|0")]]
    return await PIPE.status_text(tid), kb_rows(rows)


@app.on_message(filters.command("tasks") & filters.private & is_admin)
async def tasks_cmd(_, m):
    if not await pipe_ready(m):
        return
    text, kb = await tasks_view()
    await m.reply_text(text, parse_mode=HTML, reply_markup=kb)


@app.on_callback_query(filters.regex(r"^tk\|"))
async def on_task_button(_, cq):
    if cq.from_user.id not in config.ADMIN_IDS:
        return await cq.answer("Admin only", show_alert=True)
    if PIPE is None:
        return await cq.answer("Database not connected", show_alert=True)
    parts = cq.data.split("|")
    act, tid = parts[1], int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else 0
    note = None
    if act == "list":
        text, kb = await tasks_view()
        await safe_edit(cq.message, text, parse_mode=HTML, reply_markup=kb)
        return await cq.answer()
    if act == "pause":
        await PIPE.pause(tid)
        note = "Paused (it stops after the current episode)"
    elif act == "resume":
        await PIPE.resume(tid)
        note = "Resumed"
    elif act == "retry":
        n = await PIPE.retry(tid)
        note = f"{n} episode(s) queued again" if n else "Nothing failed"
    elif act == "bulk":
        t = await DB.task(tid)
        if not t:
            return await cq.answer("Task not found", show_alert=True)
        if not await DB.userbot():
            return await cq.answer("Log in the userbot first: /userbot", show_alert=True)
        run = PIPE.bulk.get(tid)
        if run and not run["finished"]:
            return await cq.answer("A bulk run is already going for this task", show_alert=True)
        step = "bk_first" if t.get("link_bot1") else "bk_bot1"
        WIZ[cq.from_user.id] = {"step": step, "data": {"tid": tid}}
        await cq.answer()
        return await bulk_ask(cq.message, step)
    elif act == "del":
        await safe_edit(cq.message, f"🗑 Delete task #{tid} and its saved data? Posts already made stay in the channels.",
                        reply_markup=kb_rows([[("Yes, delete", f"tk|delok|{tid}"), ("No", f"tk|open|{tid}")]]))
        return await cq.answer()
    elif act == "delok":
        await PIPE.delete(tid)
        text, kb = await tasks_view()
        await safe_edit(cq.message, text, parse_mode=HTML, reply_markup=kb)
        return await cq.answer("Deleted")
    text, kb = await task_view(tid)
    await safe_edit(cq.message, text, parse_mode=HTML, reply_markup=kb)
    await cq.answer(note)


# ------------------------------------------------------------------ bulk links for old files
BK_TEXT = {
    "bk_bot1": "🔗 <b>Bulk links</b> — this task has no link bots yet.\n🤖 <b>Link bot 1</b>: send its @username (the file-share bot with /univarsal_link).",
    "bk_post": "📣 <b>Post channel</b> — same post as the episode post, but the button is the generated link.\n" + CH_HELP,
    "bk_first": "⏮ Forward me the <b>FIRST</b> file message (the earliest file to get a link) from the file channel, or send its message link.",
    "bk_last": "⏭ Now forward the <b>LAST</b> file message (the newest one to get a link), or send its message link.",
}


async def bulk_ask(target, step):
    if step == "bk_bot2":
        return await target.reply_text("🤖 <b>Link bot 2</b>: send its @username (turns bot 1's link into the final link).",
                                       parse_mode=HTML, reply_markup=kb_rows([[("⏭ No bot 2", "bk|b2skip")]]))
    await target.reply_text(BK_TEXT[step] + "\n\n/cancel to stop.", parse_mode=HTML)


def fwd_info(m):
    """(chat id or @username, message id) of a forwarded channel message, or of a t.me link in the text."""
    ch, mid = getattr(m, "forward_from_chat", None), getattr(m, "forward_from_message_id", None)
    if ch and mid:
        return ch.id, mid
    o = getattr(m, "forward_origin", None)
    if o and getattr(o, "chat", None) and getattr(o, "message_id", None):
        return o.chat.id, o.message_id
    t = m.text or ""
    r = re.search(r"t\.me/c/(\d+)/(\d+)", t)
    if r:
        return int("-100" + r.group(1)), int(r.group(2))
    r = re.search(r"t\.me/([A-Za-z0-9_]{4,})/(\d+)", t)
    if r:
        return "@" + r.group(1), int(r.group(2))
    return None


in_bulk = filters.create(lambda _, __, m: bool(m.from_user) and WIZ.get(m.from_user.id, {}).get("step") in ("bk_first", "bk_last"))


async def bulk_range(m):
    w = WIZ[m.from_user.id]
    d = w["data"]
    t = await DB.task(d["tid"])
    info = fwd_info(m)
    if not t or not info:
        return await m.reply_text("❌ Forward the file message from the file channel (or send its message link).")
    chat, mid = info
    if isinstance(chat, str):
        try:
            chat = (await app.get_chat(chat)).id
        except Exception:
            return await m.reply_text("❌ I can't read that channel link. Forward the message instead.")
    if chat != t["file_channel"]["id"]:
        return await m.reply_text(f"❌ That message is not from this task's file channel ({esc(chan_name(t['file_channel']))}).",
                                  parse_mode=HTML)
    if w["step"] == "bk_first":
        d["first"], w["step"] = mid, "bk_last"
        await m.reply_text(f"✅ First file: message {mid}")
        return await bulk_ask(m, "bk_last")
    if mid < d["first"]:
        return await m.reply_text("❌ The last message must come after the first one. Forward it again.")
    d["last"] = mid
    eps = await PIPE.bulk_plan(d["tid"], d["first"], d["last"])
    files = [f for e in eps for f in e["files"]]
    todo = sum(1 for f in files if not f.get("link1"))
    if not eps:
        WIZ.pop(m.from_user.id, None)
        return await m.reply_text("No finished episodes of this task have files in that range.")
    w["step"] = "bk_confirm"
    lo, hi = todo * 20 / 3600, todo * 60 / 3600
    await m.reply_text(
        f"🔗 <b>Bulk links · task #{d['tid']}</b>\nMessages {d['first']} → {d['last']}\n"
        f"Episodes: {len(eps)} · files: {len(files)} (already have links: {len(files) - todo})\n"
        f"Rough time: {lo:.1f}–{hi:.1f} h for {todo} files, or {len(files) * 20 / 3600:.1f}–{len(files) * 60 / 3600:.1f} h for all "
        "(about 20–60 s per file).\n\n"
        "For each episode: new links via the userbot → file caption rebuilt with them → post channel post made (blurred image, "
        "buttons = final link) or its buttons replaced if it already exists. Episode and sub channel posts stay as they are.",
        parse_mode=HTML, reply_markup=kb_rows([[("🔄 Start · replace ALL links", "bk|go")],
                                               [("➕ Only files without links", "bk|new")],
                                               [("❌ Cancel", "bk|cancel")]]))


@app.on_message(filters.private & is_admin & in_bulk & ~filters.regex(r"^/"), group=-1)
async def bulk_range_msg(_, m):
    await bulk_range(m)
    m.stop_propagation()


@app.on_callback_query(filters.regex(r"^bk\|"))
async def on_bulk_button(_, cq):
    uid = cq.from_user.id
    if uid not in config.ADMIN_IDS:
        return await cq.answer("Admin only", show_alert=True)
    parts = cq.data.split("|")
    act = parts[1]
    if act == "stop":
        ok = PIPE.bulk_stop(int(parts[2]))
        return await cq.answer("Stopping after the current episode" if ok else "Not running")
    w = WIZ.get(uid)
    if not w:
        return await cq.answer("This setup expired. Open /tasks again.", show_alert=True)
    d = w["data"]
    if act == "cancel":
        WIZ.pop(uid, None)
        await safe_edit(cq.message, "Cancelled.")
        return await cq.answer()
    if act == "b2skip" and w["step"] == "bk_bot2":
        d["link_bot2"], w["step"] = None, "bk_post"
        await safe_edit(cq.message, "🤖 Link bot 2: <b>none</b>", parse_mode=HTML)
        await cq.answer()
        return await bulk_ask(cq.message, "bk_post")
    if act in ("go", "new") and w["step"] == "bk_confirm":
        WIZ.pop(uid, None)
        prog = await cq.message.reply_text("🔗 Bulk links starting…")
        try:
            await PIPE.bulk_start(d["tid"], d["first"], d["last"], prog.chat.id, prog.id, force=(act == "go"))
        except Exception as e:
            return await prog.edit_text(f"❌ {esc(str(e))}", parse_mode=HTML)
        await safe_edit(cq.message, "✅ Started — progress is in the next message.")
        return await cq.answer()
    await cq.answer()


# ------------------------------------------------------------------ templates
@app.on_message(filters.command("templates") & filters.private & is_admin)
async def templates_cmd(_, m):
    if not await pipe_ready(m):
        return
    parts = []
    for name, label in T.TEMPLATE_NAMES.items():
        parts.append(f"▸ {label} — change with /set_{name}_template\n{await DB.template(name)}")
    await m.reply_text("\n\n".join(parts), parse_mode=RAW)
    await m.reply_text("Variables:\n" + variables_text() + "\n\n<text> = bold · <q>text</q> = quote · [label](https://link) = link",
                       parse_mode=RAW)


async def save_template(m, name, text):
    problems = T.check_template(text)
    if problems:
        return await m.reply_text("❌ " + "; ".join(problems) + "\nSend the template again, or /cancel.")
    WIZ.pop(m.from_user.id, None)
    await DB.set_template(name, text)
    try:
        await m.reply_text("✅ Saved. Preview:\n\n" + T.render(text, T.SAMPLE), parse_mode=HTML)
    except Exception as e:
        await m.reply_text(f"⚠️ Saved, but Telegram could not display the preview ({e}). Check the template.")


@app.on_message(filters.command(["set_sub_template", "set_episode_template", "set_file_template"]) & filters.private & is_admin)
async def set_template_cmd(_, m):
    if not await pipe_ready(m):
        return
    name = m.command[0].split("_")[1]
    inline = m.text.split(None, 1)[1] if len(m.text.split(None, 1)) > 1 else ""
    if inline.strip():
        return await save_template(m, name, inline)
    WIZ[m.from_user.id] = {"step": "tpl", "name": name}
    await m.reply_text(f"✏️ New template for the {T.TEMPLATE_NAMES[name]}.\nSend the whole text in one message "
                       f"(or /cancel). Current one:\n\n{await DB.template(name)}\n\nVariables:\n{variables_text()}",
                       parse_mode=RAW)


@app.on_message(filters.command("reset_templates") & filters.private & is_admin)
async def reset_templates_cmd(_, m):
    if await pipe_ready(m):
        await DB.reset_templates()
        await m.reply_text("✅ All templates are back to the defaults.")


@app.on_message(filters.command(ADMIN_NAMES) & filters.private & ~is_admin)
async def not_admin(_, m):
    await m.reply_text("🔒 This command is for the bot admins only." if config.ADMIN_IDS
                       else "🔒 No admins are configured. Put your Telegram id in ADMIN_IDS in the .env file.")


# ------------------------------------------------------------------ startup
async def init_slot(i):
    """Start Chrome + log in, one slot at a time (staggered), then offer the slot to jobs."""
    await asyncio.sleep(i * 4)
    job = {"t0": time.time(), "tag": f"warm{i}", "step": "warmup"}
    try:
        await asyncio.get_running_loop().run_in_executor(EXECUTORS[i], SCRAPERS[i], {"kind": "warmup", "job": job})
        logging.info("browser %d ready, logged in", i)
    except Exception as e:
        logging.warning("browser %d warmup failed (its first job will retry): %s", i, e)
    SLOTS.put_nowait(i)


async def main():
    global SLOTS, TRANSFERS, DB, PIPE
    loop = asyncio.get_running_loop()
    loop.set_default_executor(ThreadPoolExecutor(max_workers=32))  # downloads / ffmpeg / thumbnails
    SLOTS = asyncio.Queue()
    TRANSFERS = asyncio.Semaphore(config.MAX_TRANSFERS)
    EXECUTORS.extend(ThreadPoolExecutor(max_workers=1) for _ in range(config.BROWSER_WORKERS))
    async def pipe_scrape(kind, url):
        return await run_scrape(NullMsg(), new_job(), {"kind": kind, "url": url})

    if config.MONGO_URI:
        try:
            DB = Store(AsyncIOMotorClient(config.MONGO_URI)[config.MONGO_DB])
            await DB.init()
            deps = SimpleNamespace(
                scrape=pipe_scrape, fetch=fetch, fetch_image=fetch_image, video_meta=video_meta, transfers=TRANSFERS,
                delay=config.PIPELINE_DELAY, max_size=config.MAX_SIZE, download_dir=config.DOWNLOAD_DIR)
            PIPE = Pipeline(app, DB, deps)
        except Exception:
            logging.exception("MongoDB is not reachable: the admin pipeline is disabled")
            DB = PIPE = None
    else:
        logging.warning("MONGO_URI is not set: the admin pipeline is disabled")
    await app.start()
    if PIPE:
        await PIPE.start_loop()  # resumes running tasks by itself after a restart
    await register_commands()
    for i in range(config.BROWSER_WORKERS):
        asyncio.create_task(init_slot(i))
    await idle()
    await app.stop()


if __name__ == "__main__":
    asyncio.run(main())