"""
TEST BOT + MINI APP (aiogram 3.x + aiohttp)

Muhit o'zgaruvchilari (Railway -> Variables):
    BOT_TOKEN   - BotFather tokeni
    WEBAPP_URL  - Railway bergan https havola (oxirida / siz)
    DB_PATH     - (ixtiyoriy) baza fayli, masalan /data/tests2.db (Volume ulansa)
    CACHE_DIR   - (ixtiyoriy) fayllar keshi, masalan /data/filecache (Volume ulansa)
    TZ_OFFSET   - (ixtiyoriy) mahalliy vaqt soat farqi, standart 5 (O'zbekiston)
    PORT        - Railway o'zi beradi

Ishga tushirish:  python bot2.py
"""
import asyncio
import calendar
import csv
import datetime
import hashlib
import hmac
import html
import io
import json
import logging
import os
import random
import re
import sqlite3
import string
import time
import zipfile
from collections import Counter
from urllib.parse import parse_qsl

from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramBadRequest
from aiogram.filters import Command, CommandObject, CommandStart, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    BufferedInputFile,
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    KeyboardButton,
    Message,
    ReplyKeyboardMarkup,
    WebAppInfo,
)

BOT_TOKEN = os.getenv("BOT_TOKEN", "")
WEBAPP_URL = os.getenv("WEBAPP_URL", "").rstrip("/")
PORT = int(os.getenv("PORT", "8080"))
DB_PATH = os.getenv("DB_PATH", "tests2.db")
CACHE_DIR = os.getenv("CACHE_DIR", "filecache")
TZ_OFFSET = float(os.getenv("TZ_OFFSET", "5"))  # mahalliy vaqt (soat), O'zbekiston = 5

PENALTY = 1  # har bir chiqib ketish uchun ayriladigan ball
GRACE = 1.5  # shuncha soniyadan qisqa uzilish jarima emas (bildirishnoma va h.k.)
DOCX_MIME = "application/vnd.openxmlformats-officedocument.wordprocessingml.document"

# ----------------------------- BAZA -----------------------------
db = sqlite3.connect(DB_PATH, check_same_thread=False)
db.row_factory = sqlite3.Row
db.executescript(
    """
CREATE TABLE IF NOT EXISTS tests(
    code TEXT PRIMARY KEY, owner_id INTEGER, title TEXT, file_id TEXT,
    kind TEXT, answer_key TEXT, minutes INTEGER, created REAL, body TEXT, questions TEXT,
    shuffle INTEGER DEFAULT 0, closed INTEGER DEFAULT 0, opens_at REAL, closes_at REAL);
CREATE TABLE IF NOT EXISTS attempts(
    code TEXT, user_id INTEGER, name TEXT, started REAL,
    finished INTEGER DEFAULT 0, correct INTEGER DEFAULT 0, total INTEGER DEFAULT 0,
    penalties INTEGER DEFAULT 0, score INTEGER DEFAULT 0,
    answers TEXT DEFAULT '{}', left_at REAL, result TEXT, last_seen REAL, finished_at REAL,
    PRIMARY KEY(code, user_id));
CREATE TABLE IF NOT EXISTS attempts_old(
    code TEXT, user_id INTEGER, name TEXT, started REAL, finished INTEGER, correct INTEGER,
    total INTEGER, penalties INTEGER, score INTEGER, answers TEXT, left_at REAL, result TEXT,
    last_seen REAL, finished_at REAL, archived REAL);
"""
)


for _col in ("body", "questions"):  # eski bazalar uchun yangi ustunlar
    try:
        db.execute(f"ALTER TABLE tests ADD COLUMN {_col} TEXT")
        db.commit()
    except sqlite3.OperationalError:
        pass


try:  # eski bazalar uchun: oxirgi faollik vaqti
    db.execute("ALTER TABLE attempts ADD COLUMN last_seen REAL")
    db.commit()
except sqlite3.OperationalError:
    pass


for _tbl, _col in (
    ("tests", "shuffle INTEGER DEFAULT 0"),
    ("tests", "closed INTEGER DEFAULT 0"),
    ("tests", "opens_at REAL"),
    ("tests", "closes_at REAL"),
    ("attempts", "finished_at REAL"),
):  # eski bazalar uchun yangi ustunlar
    try:
        db.execute(f"ALTER TABLE {_tbl} ADD COLUMN {_col}")
        db.commit()
    except sqlite3.OperationalError:
        pass


def touch(code, uid):
    """Yechuvchi ilovada faol ekanini belgilaydi."""
    db.execute(
        "UPDATE attempts SET last_seen=? WHERE code=? AND user_id=? AND finished=0",
        (time.time(), code, uid),
    )
    db.commit()


def get_test(code):
    return db.execute("SELECT * FROM tests WHERE code=?", (code,)).fetchone()


def get_attempt(code, uid):
    return db.execute(
        "SELECT * FROM attempts WHERE code=? AND user_id=?", (code, uid)
    ).fetchone()


def fmt_dt(ts: float) -> str:
    return time.strftime("%d.%m %H:%M", time.gmtime(ts + TZ_OFFSET * 3600))


def has_old(code, uid) -> bool:
    return db.execute(
        "SELECT 1 FROM attempts_old WHERE code=? AND user_id=? LIMIT 1", (code, uid)
    ).fetchone() is not None


def start_block(test, uid=None):
    """Yangi yechuvchiga test yopiq/ochilmagan bo'lsa sabab matnini qaytaradi."""
    if uid is not None and has_old(test["code"], uid):
        return None  # qayta yechishga ruxsat berilgan
    now = time.time()
    if test["closed"]:
        return "🔒 Bu test yopilgan."
    if test["opens_at"] and now < test["opens_at"]:
        return f"⏳ Test hali ochilmagan. Ochilish vaqti: {fmt_dt(test['opens_at'])}"
    if test["closes_at"] and now > test["closes_at"]:
        return "🔒 Bu testning qabul vaqti tugagan."
    return None


def rank_of(code, uid):
    rows = db.execute(
        "SELECT user_id FROM attempts WHERE code=? AND finished=1 "
        "ORDER BY score DESC, COALESCE(finished_at, 1e18) ASC",
        (code,),
    ).fetchall()
    ids = [r["user_id"] for r in rows]
    return (ids.index(uid) + 1 if uid in ids else None), len(ids)


# ----------------------------- YORDAMCHI -----------------------------
def parse_answers(text: str) -> dict:
    """'abcd' yoki '1a 2b 3c' yoki '1-a,2-b' -> {raqam: harf}"""
    text = text.strip().lower()
    pairs = re.findall(r"(\d+)\s*[-.:)]*\s*([a-z])", text)
    if pairs:
        return {int(n): l for n, l in pairs}
    return {i + 1: l for i, l in enumerate(re.findall(r"[a-z]", text))}


# Raqam belgisi (savol tartibi) yoki harf belgisi (variant): "7." / "A." / "B)" / "C,"
TOKEN_RE = re.compile(
    r"(?<!\d)(\d{1,3})\s*[.)](?!\d)"
    r"|(?<![A-Za-z0-9'ʻʼ’`])([A-Ja-j])\s*[.),]"
)


def _clean(s: str, keep_items: bool = False) -> str:
    lines = [re.sub(r"\s+", " ", ln).strip() for ln in s.split("\n")]
    lines = [ln for ln in lines if ln]
    if not lines:
        return ""
    out = lines[0]
    for ln in lines[1:]:
        sep = "\n" if keep_items and re.match(r"\d{1,3}\s*[.)]", ln) else " "
        out += sep + ln
    return out


def parse_quiz(text: str):
    """
    Savollarni matndan ajratadi. Qatorlarga bo'lingan ham, hammasi bir qatorda
    ketma-ket yozilgan ("7. savol? A.bir B.ikki C.uch D.to'rt 8. savol? ...") ham ishlaydi.
    Qoida: yangi savol raqami ketma-ket bo'lishi va oldingi savolda kamida 2 ta variant
    bo'lishi kerak; variant harflari A, B, C... tartibida kelishi kerak.
    """
    t = text.replace("\r", "")
    qs, cur = [], None
    kind, start = None, 0  # hozirgi bo'lak: "q" yoki variant harfi

    def close(end):
        chunk = t[start:end]
        if kind == "q":
            cur["t"] = _clean(chunk, keep_items=True)
        elif kind:
            cur["o"][kind] = _clean(chunk)

    for m in TOKEN_RE.finditer(t):
        num, let = m.group(1), m.group(2)
        if num is not None:
            if int(num) == len(qs) + 1 and (cur is None or cur["n"] >= 2):
                if cur is not None:
                    close(m.start())
                cur = {"q": len(qs) + 1, "t": "", "o": {}, "n": 0}
                qs.append(cur)
                kind, start = "q", m.end()
            continue
        if cur is None:
            continue
        expect = chr(ord("a") + cur["n"])
        if let.lower() == expect:
            close(m.start())
            cur["n"] += 1
            kind, start = expect, m.end()
    if cur is not None:
        close(len(t))
    if not qs or any(len(q["o"]) < 2 or not q["t"] for q in qs):
        return None
    for q in qs:
        q.pop("n", None)
    return qs


def qdata_for(test):
    if test["kind"] != "quiz" or not test["questions"]:
        return None
    return json.loads(test["questions"])


def docx_to_text(data: bytes):
    """Word (.docx) ichidagi matnni oladi (qo'lda yozilgan raqam/harflar uchun)."""
    try:
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            xml = z.read("word/document.xml").decode("utf-8", "ignore")
    except Exception:
        return None
    out = []
    for p in re.findall(r"<w:p[ >].*?</w:p>", xml, re.S):
        p = re.sub(r"<w:tab\s*/>", " ", p)
        p = re.sub(r"<w:br\s*/>", "\n", p)
        txt = "".join(re.findall(r"<w:t(?:\s[^>]*)?>(.*?)</w:t>", p, re.S))
        out.append(html.unescape(txt))
    return "\n".join(out)


def quiz_note(qs) -> str:
    sizes = [len(q["o"]) for q in qs]
    common = max(set(sizes), key=sizes.count)
    odd = [str(q["q"]) for q in qs if len(q["o"]) != common]
    note = (
        f"\n⚠️ Variantlar soni {common} tadan farq qiladigan savollar: {', '.join(odd[:20])}. Tekshirib ko'ring."
        if odd else ""
    )
    return f"✅ {len(qs)} ta savol, har birida {common} tadan variant aniqlandi.{note}"


def encode_key(d: dict) -> str:
    return ",".join(f"{n}{l}" for n, l in sorted(d.items()))


def decode_key(s: str) -> dict:
    return {int(p[:-1]): p[-1] for p in s.split(",") if p}


def new_code() -> str:
    while True:
        c = "".join(random.choices(string.ascii_uppercase + string.digits, k=6))
        if not get_test(c):
            return c


def time_left(test, att) -> float:
    return att["started"] + test["minutes"] * 60 - time.time()


def finalize(code: str, uid: int, kicked: bool = False):
    """Natijani hisoblaydi. (natija_dict, yangi_yakunlandimi) qaytaradi."""
    test, att = get_test(code), get_attempt(code, uid)
    if att["finished"] and att["result"]:
        return json.loads(att["result"]), False

    pen = att["penalties"]
    if att["left_at"] and time.time() - att["left_at"] >= GRACE:
        pen += 1  # ilovadan chiqib, qaytmagan

    key = decode_key(test["answer_key"])
    given = {int(k): v for k, v in json.loads(att["answers"] or "{}").items()}
    correct = sum(1 for n, l in key.items() if given.get(n) == l)
    total = len(key)
    score = max(0, correct - pen * PENALTY)
    wrong = [
        {"q": n, "given": given.get(n, ""), "right": l}
        for n, l in sorted(key.items())
        if given.get(n) != l
    ]
    res = {
        "title": test["title"],
        "correct": correct,
        "total": total,
        "penalties": pen * PENALTY,
        "score": score,
        "wrong": wrong,
        "kicked": kicked,
        "items": [
            {"q": n, "given": given.get(n, ""), "right": l}
            for n, l in sorted(key.items())
        ],
    }
    db.execute(
        "UPDATE attempts SET finished=1, correct=?, total=?, penalties=?, score=?, "
        "left_at=NULL, result=?, finished_at=? WHERE code=? AND user_id=?",
        (correct, total, pen, score, json.dumps(res), time.time(), code, uid),
    )
    db.commit()
    return res, True


def bar(pct: int, n: int = 10) -> str:
    k = max(0, min(n, round(pct / 100 * n)))
    return "▰" * k + "▱" * (n - k)


def result_text(r: dict, rank=None) -> str:
    total = r["total"]
    pct = round(r["score"] / total * 100) if total else 0
    t = (
        f"📊 <b>{html.escape(r['title'])}</b>\n\n"
        f"{bar(pct)}  <b>{pct}%</b>\n\n"
        f"✅ To'g'ri javoblar: <b>{r['correct']}/{total}</b>\n"
        f"🚪 Chiqib ketish jarimasi: -{r['penalties']}\n"
        f"🏆 Yakuniy ball: <b>{r['score']}</b>\n"
    )
    if rank and rank[0]:
        t += f"📈 Hozirgi reyting: <b>{rank[0]}-o'rin</b> ({rank[1]} kishidan)\n"
    if r.get("kicked"):
        t += "🚫 Test egasi tomonidan tugatildi\n"
    w = r["wrong"]
    if w:
        lines = [
            f"{x['q']}) siz: {(x['given'] or '—').upper()} → to'g'ri: {x['right'].upper()}"
            for x in w[:60]
        ]
        t += "\n❌ <b>Xatolar:</b>\n" + "\n".join(lines)
        if len(w) > 60:
            t += f"\n... va yana {len(w) - 60} ta"
    else:
        t += "\n🎉 Xatosiz! Barakalla!"
    return t


async def notify_owner(bot: Bot, code: str, uid: int):
    test, att = get_test(code), get_attempt(code, uid)
    try:
        await bot.send_message(
            test["owner_id"],
            f"🔔 <b>{html.escape(test['title'])}</b> ({code})\n"
            f"{html.escape(att['name'] or '')} tugatdi: {att['correct']}/{att['total']}, "
            f"jarima: -{att['penalties'] * PENALTY}, ball: <b>{att['score']}</b>",
        )
    except Exception:
        pass


def review_kb(code: str):
    if not WEBAPP_URL:
        return None
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="🔍 Xatolarni tahlil qilish", web_app=WebAppInfo(url=f"{WEBAPP_URL}/app?code={code}"))]
        ]
    )


async def conclude(bot: Bot, code: str, uid: int, prefix: str = "", kicked: bool = False) -> dict:
    res, new = finalize(code, uid, kicked)
    if new:
        try:
            await bot.send_message(
                uid, prefix + result_text(res, rank_of(code, uid)), reply_markup=review_kb(code)
            )
        except Exception:
            pass
        if not kicked:
            await notify_owner(bot, code, uid)
    return res


async def timer_task(bot: Bot, code: str, uid: int, delay: float = 0):
    """Tugash vaqtini doim bazadan qayta tekshiradi (vaqt uzaytirilishi mumkin)."""
    warned = False
    while True:
        att, test = get_attempt(code, uid), get_test(code)
        if not att or att["finished"]:
            return
        left = time_left(test, att)
        if left <= 0:
            break
        if left > 70:
            warned = False
        if left <= 60 and not warned and test["minutes"] * 60 > 120:
            warned = True
            try:
                await bot.send_message(uid, "⏰ Vaqtning tugashiga 1 daqiqa qoldi!")
            except Exception:
                pass
        await asyncio.sleep(min(left - 60, 20) if left > 60 else min(left, 5))
    att = get_attempt(code, uid)
    if att and not att["finished"]:
        await conclude(bot, code, uid, "⌛ Vaqt tugadi.\n\n")


def resume_timers(bot: Bot):
    """Bot qayta ishga tushganda tugamagan urinishlar taymerini tiklaydi."""
    rows = db.execute(
        "SELECT a.code, a.user_id, a.started, t.minutes FROM attempts a "
        "JOIN tests t ON t.code=a.code WHERE a.finished=0"
    ).fetchall()
    for r in rows:
        left = r["started"] + r["minutes"] * 60 - time.time()
        asyncio.create_task(timer_task(bot, r["code"], r["user_id"], left))


# ----------------------------- MINI APP: AUTH -----------------------------
def check_init_data(init_data: str):
    """Telegram initData imzosini tekshiradi, foydalanuvchini qaytaradi."""
    try:
        pairs = dict(parse_qsl(init_data, keep_blank_values=True))
        h = pairs.pop("hash", None)
        if not h:
            return None
        check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, h):
            return None
        if time.time() - int(pairs.get("auth_date", "0")) > 86400:
            return None
        return json.loads(pairs["user"])
    except Exception:
        return None


async def read_body(request) -> dict:
    try:
        return json.loads(await request.text() or "{}")
    except Exception:
        raise web.HTTPBadRequest(text="Noto'g'ri so'rov")


def auth(d: dict):
    user = check_init_data(d.get("init", ""))
    if not user:
        raise web.HTTPUnauthorized(text="Sahifani Telegram bot orqali oching")
    name = f"{user.get('first_name', '')} {user.get('last_name', '')}".strip()
    return user["id"], name


# ----------------------------- MINI APP: API -----------------------------
async def api_start(request):
    d = await read_body(request)
    uid, name = auth(d)
    code = str(d.get("code", "")).upper()
    test = get_test(code)
    if not test:
        raise web.HTTPNotFound(text="Test topilmadi")
    bot = request.app["bot"]

    att = get_attempt(code, uid)
    if att and att["finished"]:
        res, _ = finalize(code, uid)
        return web.json_response({"finished": True, "result": res, "kind": test["kind"], "qdata": qdata_for(test), "shuffle": test["shuffle"] or 0, "seed": f"{code}:{uid}"})

    new = att is None
    if new:
        block = start_block(test, uid)
        if block:
            raise web.HTTPConflict(text=block)
        db.execute(
            "INSERT INTO attempts(code,user_id,name,started) VALUES(?,?,?,?)",
            (code, uid, name, time.time()),
        )
        db.commit()
    elif att["left_at"]:  # yopib, qayta ochgan
        pen = att["penalties"] + (1 if time.time() - att["left_at"] >= GRACE else 0)
        db.execute(
            "UPDATE attempts SET penalties=?, left_at=NULL WHERE code=? AND user_id=?",
            (pen, code, uid),
        )
        db.commit()
    att = get_attempt(code, uid)
    touch(code, uid)

    left = time_left(test, att)
    if left <= 0:
        res = await conclude(bot, code, uid, "⌛ Vaqt tugadi.\n\n")
        return web.json_response({"finished": True, "result": res, "kind": test["kind"], "qdata": qdata_for(test), "shuffle": test["shuffle"] or 0, "seed": f"{code}:{uid}"})
    if new:
        asyncio.create_task(timer_task(bot, code, uid, left))

    key = decode_key(test["answer_key"])
    last = max(max(key.values()), "d")
    options = [chr(c) for c in range(ord("a"), ord(last) + 1)]
    return web.json_response(
        {
            "finished": False,
            "title": test["title"],
            "kind": test["kind"],
            "qdata": qdata_for(test),
            "shuffle": test["shuffle"] or 0,
            "seed": f"{code}:{uid}",
            "questions": sorted(key.keys()),
            "options": options,
            "left": left,
            "answers": json.loads(att["answers"] or "{}"),
            "penalties": att["penalties"] * PENALTY,
        }
    )


async def get_file_bytes(bot: Bot, test) -> bytes:
    if test["kind"] in ("text", "quiz"):
        return (test["body"] or "").encode("utf-8")
    os.makedirs(CACHE_DIR, exist_ok=True)
    path = os.path.join(CACHE_DIR, test["code"])
    if os.path.exists(path):
        with open(path, "rb") as f:
            return f.read()
    buf = io.BytesIO()
    await bot.download(test["file_id"], destination=buf)
    data = buf.getvalue()
    with open(path, "wb") as f:
        f.write(data)
    return data


async def api_file(request):
    d = await read_body(request)
    uid, _ = auth(d)
    code = str(d.get("code", "")).upper()
    test, att = get_test(code), get_attempt(code, uid)
    if not test or not att:
        raise web.HTTPForbidden(text="Ruxsat yo'q")
    data = await get_file_bytes(request.app["bot"], test)
    return web.Response(body=data, content_type="application/octet-stream")


async def api_answer(request):
    d = await read_body(request)
    uid, _ = auth(d)
    code = str(d.get("code", "")).upper()
    touch(code, uid)
    test, att = get_test(code), get_attempt(code, uid)
    if not test or not att or att["finished"] or time_left(test, att) <= 0:
        raise web.HTTPConflict(text="expired")
    key = decode_key(test["answer_key"])
    try:
        q = int(d.get("q"))
    except Exception:
        raise web.HTTPBadRequest(text="Noto'g'ri savol")
    a = str(d.get("a", "")).lower()[:1]
    if q not in key:
        raise web.HTTPBadRequest(text="Noto'g'ri savol")
    ans = json.loads(att["answers"] or "{}")
    if a:
        ans[str(q)] = a
    else:
        ans.pop(str(q), None)
    db.execute(
        "UPDATE attempts SET answers=? WHERE code=? AND user_id=?",
        (json.dumps(ans), code, uid),
    )
    db.commit()
    return web.json_response({"ok": True})


async def api_leave(request):
    d = await read_body(request)
    uid, _ = auth(d)
    code = str(d.get("code", "")).upper()
    touch(code, uid)
    att = get_attempt(code, uid)
    if att and not att["finished"] and not att["left_at"]:
        db.execute(
            "UPDATE attempts SET left_at=? WHERE code=? AND user_id=?",
            (time.time(), code, uid),
        )
        db.commit()
    return web.json_response({"ok": True})


async def api_back(request):
    d = await read_body(request)
    uid, _ = auth(d)
    code = str(d.get("code", "")).upper()
    touch(code, uid)
    test, att = get_test(code), get_attempt(code, uid)
    if not test or not att:
        raise web.HTTPNotFound(text="Topilmadi")
    if att["finished"]:
        res, _ = finalize(code, uid)
        return web.json_response({"finished": True, "result": res})

    pen, penalized = att["penalties"], False
    if att["left_at"]:
        if time.time() - att["left_at"] >= GRACE:
            pen += 1
            penalized = True
        db.execute(
            "UPDATE attempts SET penalties=?, left_at=NULL WHERE code=? AND user_id=?",
            (pen, code, uid),
        )
        db.commit()
        att = get_attempt(code, uid)

    left = time_left(test, att)
    if left <= 0:
        res = await conclude(request.app["bot"], code, uid, "⌛ Vaqt tugadi.\n\n")
        return web.json_response({"finished": True, "result": res})
    return web.json_response(
        {"finished": False, "penalties": pen * PENALTY, "penalized": penalized, "left": left}
    )


async def api_submit(request):
    d = await read_body(request)
    uid, _ = auth(d)
    code = str(d.get("code", "")).upper()
    if not get_test(code) or not get_attempt(code, uid):
        raise web.HTTPNotFound(text="Topilmadi")
    res = await conclude(request.app["bot"], code, uid)
    return web.json_response({"result": res})


async def api_sync(request):
    d = await read_body(request)
    uid, _ = auth(d)
    code = str(d.get("code", "")).upper()
    touch(code, uid)
    test, att = get_test(code), get_attempt(code, uid)
    if not test or not att:
        raise web.HTTPNotFound(text="Topilmadi")
    if att["finished"]:
        res, _ = finalize(code, uid)
        return web.json_response({"finished": True, "result": res})
    left = time_left(test, att)
    if left <= 0:
        res = await conclude(request.app["bot"], code, uid, "⌛ Vaqt tugadi.\n\n")
        return web.json_response({"finished": True, "result": res})
    return web.json_response({"finished": False, "left": left})


async def health(request):
    return web.Response(text="OK")


async def page(request):
    return web.Response(
        text=HTML, content_type="text/html", headers={"Cache-Control": "no-store"}
    )


def make_web(bot: Bot) -> web.Application:
    app = web.Application()
    app["bot"] = bot
    app.add_routes(
        [
            web.get("/", health),
            web.get("/app", page),
            web.post("/api/start", api_start),
            web.post("/api/file", api_file),
            web.post("/api/answer", api_answer),
            web.post("/api/leave", api_leave),
            web.post("/api/back", api_back),
            web.post("/api/submit", api_submit),
            web.post("/api/sync", api_sync),
        ]
    )
    return app


# ----------------------------- MINI APP: SAHIFA -----------------------------
HTML = r"""<!DOCTYPE html>
<html lang="uz"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=5, viewport-fit=cover">
<title>Test</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Plus+Jakarta+Sans:wght@400;600;700&display=swap" rel="stylesheet">
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/mammoth/1.6.0/mammoth.browser.min.js"></script>
<style>
:root{--bg:var(--tg-theme-bg-color,#fff);--tx:var(--tg-theme-text-color,#111);--hint:var(--tg-theme-hint-color,#888);--btn:var(--tg-theme-button-color,#2481cc);--btx:var(--tg-theme-button-text-color,#fff);--sec:var(--tg-theme-secondary-bg-color,#f1f1f1)}
:root{--qbg:#f5f6fb;--qtx:#151a4a;--qcard:#fff;--qline:#e3e5f0;--qsoft:#eceef8;--qsel:#eef0ff;--pri:#5b67e8;--curbg:#161a4d;--qmuted:#8a8fb0;--goodbg:#e8f7ea;--badbg:#fdeaea;--qshadow:rgba(30,36,100,.08)}
body.dark{--qbg:#0e1022;--qtx:#e9ebff;--qcard:#191d3b;--qline:#2b3060;--qsoft:#252a52;--qsel:#232b6b;--curbg:#5b67e8;--qmuted:#8f95c4;--goodbg:#12311c;--badbg:#3a1a20;--qshadow:rgba(0,0,0,.35)}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--tx);font:16px/1.4 "Plus Jakarta Sans",-apple-system,system-ui,sans-serif}
.hidden{display:none!important}
.center{padding:40px 20px;text-align:center}
header{position:sticky;top:0;z-index:5;background:var(--bg);border-bottom:1px solid var(--sec);padding:8px 12px}
.r1{display:flex;justify-content:space-between;align-items:center;gap:8px}
#title{font-weight:600;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
#timer{font-variant-numeric:tabular-nums;font-weight:700;font-size:18px}
#timer.low{color:#e53935}
#pen{font-size:13px;color:#e53935;min-height:16px}
.tabs{display:flex;gap:8px;margin-top:6px}
.tab{flex:1;padding:8px;border-radius:10px;border:0;background:var(--sec);color:var(--tx);font-size:15px}
.tab.on{background:var(--btn);color:var(--btx)}
main{padding-bottom:90px}
#doc,#doc2{background:#fff;color:#000;min-height:200px}
#doc canvas,#doc2 canvas{display:block;margin:0 auto 6px}
.q.bad{background:rgba(229,57,53,.10)}
.qwrap{background:var(--qbg);color:var(--qtx);min-height:100vh;padding:14px 14px 40px;transition:background .3s}
.qhead{background:linear-gradient(135deg,#161a4d,#2d33a0);color:#fff;border-radius:18px;padding:12px 14px;display:flex;justify-content:space-between;gap:10px;font-size:14px;box-shadow:0 8px 20px rgba(22,26,77,.3)}
.qhead div{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.qrow{display:flex;justify-content:space-between;align-items:center;margin:14px 2px 6px;gap:10px}
.qtitle{font-weight:700;font-size:18px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;flex:1}
.qtimer{background:var(--qcard);border:1px solid var(--qline);border-radius:999px;padding:8px 14px;font-weight:700;font-variant-numeric:tabular-nums;white-space:nowrap}
.qtimer.low{color:#e53935;border-color:#e53935;animation:pulse 1s infinite}
@keyframes pulse{0%,100%{transform:scale(1)}50%{transform:scale(1.07)}}
.qwarn{font-size:13px;color:var(--qmuted);margin:0 2px 10px}
.qbar{height:8px;background:var(--qsoft);border-radius:99px;overflow:hidden;margin-bottom:14px}
.qbar i{display:block;height:100%;background:linear-gradient(90deg,var(--pri),#8a94ff);border-radius:99px;width:0;transition:width .4s ease}
.qcard{background:var(--qcard);border-radius:22px;padding:20px 16px;box-shadow:0 8px 24px var(--qshadow)}
.qcard.slide{animation:qin .28s ease}
@keyframes qin{from{opacity:0;transform:translateX(22px)}to{opacity:1;transform:none}}
.qtop{display:flex;justify-content:space-between;align-items:center;gap:8px;margin-bottom:8px}
.qnum{color:var(--pri);font-weight:600;font-size:14px}
.qtools{display:flex;gap:6px}
.tbtn{min-width:34px;height:32px;padding:0 8px;border-radius:10px;border:1px solid var(--qline);background:var(--qcard);color:var(--qtx);font-weight:700;font-size:13px}
.tbtn.on{background:#fff4d6;border-color:#f5a623;color:#9a6200}
.qtext{font-weight:700;font-size:var(--fs,18px);line-height:1.45;white-space:pre-wrap;word-wrap:break-word;margin-bottom:16px}
.opt{display:flex;align-items:center;gap:12px;width:100%;text-align:left;background:var(--qcard);border:2px solid var(--qline);border-radius:18px;padding:12px 14px;margin-bottom:10px;font-size:16px;color:var(--qtx);font-family:inherit;transition:transform .12s,border-color .15s,background .15s}
.opt:active{transform:scale(.985)}
.opt.sel{border-color:var(--pri);background:var(--qsel)}
.opt.good{border-color:#4db35a;background:var(--goodbg)}
.opt.bad{border-color:#e53935;background:var(--badbg)}
.ol{flex:none;width:34px;height:34px;border-radius:50%;background:var(--qsoft);display:flex;align-items:center;justify-content:center;font-weight:700;font-size:14px}
.opt.sel .ol{background:var(--pri);color:#fff}
.opt.good .ol{background:#4db35a;color:#fff}
.opt.bad .ol{background:#e53935;color:#fff}
.ot{flex:1;white-space:pre-wrap;word-wrap:break-word;font-size:calc(var(--fs,18px) - 2px)}
.qnav{display:flex;justify-content:space-between;margin-top:14px}
.nbtn{padding:12px 22px;border-radius:999px;border:1px solid var(--qline);background:var(--qcard);color:var(--qtx);font-size:16px;font-weight:600}
.nbtn:disabled{opacity:.4}
.nbtn.pri{background:var(--pri);color:#fff;border:0;box-shadow:0 8px 18px rgba(91,103,232,.35)}
.qgrid{display:grid;grid-template-columns:repeat(8,1fr);gap:8px;margin:18px 0 12px}
.gn{aspect-ratio:1;border-radius:12px;border:1px solid var(--qline);background:var(--qcard);color:var(--qtx);font-weight:600;font-size:14px;padding:0}
.gn.done{background:#5cc36a;border-color:#4db35a;color:#fff}
.gn.cur{background:var(--curbg);border-color:var(--curbg);color:#fff}
.gn.flag{box-shadow:inset 0 0 0 3px #f5a623}
.qleg{font-size:13px;color:var(--qmuted);display:flex;flex-wrap:wrap;gap:6px 14px;align-items:center}
.qleg i{display:inline-block;width:12px;height:12px;border-radius:4px;margin-right:4px;vertical-align:-1px}
.lg-done{background:#5cc36a}
.lg-cur{background:var(--curbg)}
.lg-none{background:var(--qcard);border:1px solid var(--qline)}
.lg-flag{background:var(--qcard);border:2px solid #f5a623}
.allmsg{margin-top:16px;padding:10px 12px;border-radius:14px;background:var(--goodbg);text-align:center;font-weight:600}
.big.pulse{animation:pulse 1.2s infinite}
.donut{position:relative;width:140px;height:140px;margin:6px auto 12px}
.donut svg{transform:rotate(-90deg)}
.donut b{position:absolute;left:0;top:0;right:0;bottom:0;display:flex;align-items:center;justify-content:center;font-size:30px}
.conf{position:fixed;top:-30px;font-size:22px;animation:fall 2.8s linear forwards;z-index:30;pointer-events:none}
@keyframes fall{to{transform:translateY(115vh) rotate(540deg)}}
.docx{padding:14px;overflow-x:auto}
.docx img{max-width:100%}
.txt{white-space:pre-wrap;font-size:17px;line-height:1.55;word-wrap:break-word}
.q{display:flex;align-items:center;gap:6px;padding:8px 12px;border-bottom:1px solid var(--sec)}
.q b{width:36px}
.o{flex:1;padding:10px 0;border-radius:10px;border:1px solid var(--hint);background:transparent;color:var(--tx);font-size:16px;text-transform:uppercase}
.o.sel{background:var(--btn);color:var(--btx);border-color:var(--btn)}
footer{position:fixed;left:0;right:0;bottom:0;background:var(--bg);border-top:1px solid var(--sec);padding:10px 12px calc(10px + env(safe-area-inset-bottom))}
.big{width:100%;padding:14px;border:0;border-radius:12px;background:var(--btn);color:var(--btx);font-size:17px;font-weight:600}
#toast{position:fixed;left:12px;right:12px;top:70px;background:#e53935;color:#fff;padding:10px 12px;border-radius:10px;z-index:20;text-align:center}
.card{margin:16px;padding:16px;border-radius:14px;background:var(--sec)}
.card h2{margin:0 0 8px}
.big-n{font-size:40px;font-weight:700}
.wrong{padding:6px 0;border-bottom:1px solid var(--bg)}
</style></head>
<body>

<div id="s-load" class="center">Yuklanmoqda...</div>

<div id="s-test" class="hidden">
  <header>
    <div class="r1"><div id="title"></div><div id="timer">--:--</div></div>
    <div id="pen"></div>
    <div class="tabs">
      <button class="tab on" id="tab-doc">📄 Test</button>
      <button class="tab" id="tab-ans">✍️ Javoblar <span id="cnt"></span></button>
    </div>
  </header>
  <main>
    <div id="v-doc"><div id="doc" class="docwrap"><div class="center" style="color:#666">Fayl yuklanmoqda...</div></div></div>
    <div id="v-ans" class="hidden"></div>
  </main>
  <footer><button class="big" id="finish">✅ Yakunlash</button></footer>
</div>

<div id="s-quiz" class="hidden qwrap">
  <div class="qhead"><div id="q-user"></div><div id="q-id"></div></div>
  <div class="qrow"><div class="qtitle" id="q-title"></div><div class="qtimer" id="qtimer">--:--</div></div>
  <div class="qwarn" id="qpen"></div>
  <div class="qbar"><i id="q-bar"></i></div>
  <div class="qcard" id="q-card">
    <div class="qtop"><div class="qnum" id="q-num"></div><div class="qtools"><button class="tbtn" id="t-small">A−</button><button class="tbtn" id="t-big">A+</button><button class="tbtn" id="t-flag">🚩</button></div></div>
    <div class="qtext" id="q-text"></div>
    <div id="q-opts"></div>
    <div class="qnav"><button class="nbtn" id="q-prev">Oldingi</button><button class="nbtn pri" id="q-next">Keyingi</button></div>
  </div>
  <div class="qgrid" id="q-grid"></div>
  <div class="qleg"><b id="q-count"></b><span>javob berildi</span><span><i class="lg-done"></i>Javob berilgan</span><span><i class="lg-cur"></i>Hozirgi savol</span><span><i class="lg-none"></i>Javobsiz</span><span><i class="lg-flag"></i>Belgilangan</span></div>
  <div class="allmsg hidden" id="q-allmsg">🎉 Hammasiga javob berildi. Yakunlashga tayyormisiz?</div>
  <div style="margin-top:18px"><button class="big" id="q-finish">✅ Testni yakunlash</button></div>
</div>

<div id="s-res" class="hidden">
  <div class="card">
    <h2 id="r-title"></h2>
    <div id="r-kick" class="hidden" style="color:#e53935;font-weight:600;margin-bottom:8px">🚫 Test egasi tomonidan tugatildi</div>
    <div class="donut" id="r-donut"></div>
    <div class="big-n" id="r-main"></div>
    <div>✅ To'g'ri javoblar</div>
    <p>🚪 Chiqib ketish jarimasi: <b id="r-pen"></b></p>
    <p>🏆 Yakuniy ball: <b id="r-score"></b></p>
  </div>
  <div class="card" id="r-wrongbox"><h2>❌ Xatolar</h2><div id="r-wrong"></div></div>
  <div style="padding:0 16px 10px"><button class="big" id="revbtn">🔍 Xatolarni tahlil qilish</button></div>
  <div style="padding:0 16px 30px"><button class="big" id="closebtn" style="background:var(--sec);color:var(--tx)">Yopish</button></div>
</div>

<div id="s-rev" class="hidden">
  <header>
    <div class="r1">
      <button class="tab" id="rev-back" style="flex:none;padding:8px 12px">← Natija</button>
      <div style="font-weight:600">Xatolar tahlili</div>
    </div>
    <div class="tabs">
      <button class="tab on" id="rt-ans">📋 Javoblar</button>
      <button class="tab" id="rt-doc">📄 Test</button>
    </div>
  </header>
  <main style="padding-bottom:20px">
    <div id="rv-ans"></div>
    <div id="rv-doc" class="hidden"><div id="doc2" class="docwrap"><div class="center" style="color:#666">Fayl yuklanmoqda...</div></div></div>
  </main>
</div>

<div id="toast" class="hidden"></div>

<script>
const tg = window.Telegram.WebApp;
tg.ready(); tg.expand();
function applyTheme() { document.body.classList.toggle("dark", tg.colorScheme === "dark"); }
applyTheme();
try { tg.onEvent("themeChanged", applyTheme); } catch (e) {}
try { if (tg.disableVerticalSwipes) tg.disableVerticalSwipes(); tg.enableClosingConfirmation(); } catch (e) {}
const INIT = tg.initData || "";
const CODE = (new URLSearchParams(location.search).get("code") || "").toUpperCase();
const $ = id => document.getElementById(id);
let S = null, finished = false, answers = {}, endAt = 0;
let away = false, ignoreAway = false, leaveP = Promise.resolve();
let warn60 = false, initialLeft = 0, SEQ = [], PERM = {}, flags = {}, flagKey = "", allShown = false, fs = 18;

function post(path, extra, keepalive) {
  return fetch(path, {
    method: "POST",
    headers: {"Content-Type": "application/json"},
    body: JSON.stringify(Object.assign({init: INIT, code: CODE}, extra || {})),
    keepalive: !!keepalive
  });
}
async function api(path, extra) {
  const r = await post(path, extra);
  if (!r.ok) throw new Error((await r.text()) || ("Xato " + r.status));
  return r.json();
}
function show(name) {
  ["load", "test", "quiz", "res", "rev"].forEach(n => $("s-" + n).classList.toggle("hidden", n !== name));
}
function toast(t) {
  const el = $("toast"); el.textContent = t; el.classList.remove("hidden");
  setTimeout(() => el.classList.add("hidden"), 3500);
}
function haptic(kind) { try { tg.HapticFeedback.notificationOccurred(kind); } catch (e) {} }
function lsGet(k) { try { return localStorage.getItem(k); } catch (e) { return null; } }
function lsSet(k, v) { try { localStorage.setItem(k, v); } catch (e) {} }
function confetti() {
  const em = ["🎉", "✨", "🎊", "⭐"];
  for (let i = 0; i < 36; i++) {
    const sp = document.createElement("span"); sp.className = "conf"; sp.textContent = em[i % em.length];
    sp.style.left = (Math.random() * 96) + "vw"; sp.style.animationDelay = (Math.random() * 0.9) + "s";
    document.body.appendChild(sp);
    setTimeout(() => { if (sp.remove) sp.remove(); }, 4200);
  }
}
function fatal(msg) { $("s-load").textContent = "❌ " + msg; }
function fmt(s) {
  s = Math.max(0, Math.floor(s));
  return String(Math.floor(s / 60)).padStart(2, "0") + ":" + String(s % 60).padStart(2, "0");
}
function setPen(p) {
  const t = p > 0 ? ("🚪 Jarima: -" + p) : "⚠️ Ilovadan chiqsangiz -1 ball";
  $("pen").textContent = t; $("qpen").textContent = t;
}

let checking = false;
async function checkEnd() {
  if (checking || finished) return;
  checking = true;
  try {
    const r = await api("/api/sync");
    if (r.finished) showResult(r.result);
    else endAt = Date.now() + r.left * 1000;
  } catch (e) {}
  checking = false;
}

function tick() {
  if (finished) return;
  const left = (endAt - Date.now()) / 1000;
  $("timer").textContent = fmt(left);
  $("timer").classList.toggle("low", left < 60);
  $("qtimer").textContent = "⏱ " + fmt(left);
  $("qtimer").classList.toggle("low", left < 60);
  if (left <= 60 && left > 0 && !warn60 && initialLeft > 120) { warn60 = true; haptic("warning"); }
  if (left > 70) warn60 = false;
  if (left <= 0) checkEnd();
}

function updateCount() {
  $("cnt").textContent = "(" + Object.keys(answers).length + "/" + S.questions.length + ")";
}

function buildSheet() {
  const box = $("v-ans");
  S.questions.forEach(q => {
    const row = document.createElement("div"); row.className = "q";
    const n = document.createElement("b"); n.textContent = q + "."; row.appendChild(n);
    S.options.forEach(l => {
      const b = document.createElement("button"); b.className = "o"; b.textContent = l;
      b.dataset.q = q; b.dataset.l = l;
      if (answers[q] === l) b.classList.add("sel");
      b.onclick = () => pick(q, l, row);
      row.appendChild(b);
    });
    box.appendChild(row);
  });
  updateCount();
}

function pick(q, l, row) {
  const nv = answers[q] === l ? "" : l;
  if (nv) answers[q] = nv; else delete answers[q];
  row.querySelectorAll(".o").forEach(b => b.classList.toggle("sel", b.dataset.l === nv));
  updateCount();
  api("/api/answer", {q: q, a: nv}).catch(e => {
    if (String(e.message).indexOf("expired") >= 0) submit(true);
    else toast("Javob saqlanmadi, qayta bosing");
  });
}

async function loadDoc(doc) {
  doc = doc || $("doc");
  try {
    const r = await post("/api/file");
    if (!r.ok) throw new Error(await r.text());
    const buf = await r.arrayBuffer();
    doc.innerHTML = "";
    if (S.kind === "text") {
      const div = document.createElement("div"); div.className = "docx txt";
      div.textContent = new TextDecoder("utf-8").decode(buf);
      doc.appendChild(div);
    } else if (S.kind === "pdf") {
      pdfjsLib.GlobalWorkerOptions.workerSrc = "https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.worker.min.js";
      const pdf = await pdfjsLib.getDocument({data: new Uint8Array(buf)}).promise;
      const cssW = doc.clientWidth || window.innerWidth;
      const dpr = Math.min(window.devicePixelRatio || 1, 2);
      for (let i = 1; i <= pdf.numPages; i++) {
        const page = await pdf.getPage(i);
        const k = cssW / page.getViewport({scale: 1}).width;
        const vp = page.getViewport({scale: k * dpr});
        const c = document.createElement("canvas");
        c.width = vp.width; c.height = vp.height;
        c.style.width = cssW + "px"; c.style.height = (vp.height / dpr) + "px";
        doc.appendChild(c);
        await page.render({canvasContext: c.getContext("2d"), viewport: vp}).promise;
      }
    } else {
      const res = await mammoth.convertToHtml({arrayBuffer: buf});
      const div = document.createElement("div"); div.className = "docx"; div.innerHTML = res.value;
      doc.appendChild(div);
    }
  } catch (e) {
    doc.innerHTML = '<div class="center" style="color:#c00">Faylni ochib bo\'lmadi.<br><br><button class="big" onclick="loadDoc(this.closest(&quot;.docwrap&quot;))">Qayta urinish</button></div>';
  }
}

let curTab = "doc";
const scrollPos = {doc: 0, ans: 0};
function setTab(t) {
  if (t === curTab) return;
  scrollPos[curTab] = window.scrollY;
  curTab = t;
  $("v-doc").classList.toggle("hidden", t !== "doc");
  $("v-ans").classList.toggle("hidden", t !== "ans");
  $("tab-doc").classList.toggle("on", t === "doc");
  $("tab-ans").classList.toggle("on", t === "ans");
  window.scrollTo(0, scrollPos[t]);
  requestAnimationFrame(() => window.scrollTo(0, scrollPos[t]));
}
$("tab-doc").onclick = () => setTab("doc");
$("tab-ans").onclick = () => setTab("ans");

let RES = null, revDocLoaded = false;
function showResult(r) {
  finished = true;
  RES = r;
  try { tg.disableClosingConfirmation(); } catch (e) {}
  $("r-title").textContent = r.title;
  $("r-kick").classList.toggle("hidden", !r.kicked);
  const pct = r.total ? Math.round(r.score / r.total * 100) : 0;
  const col = pct >= 80 ? "#2fb344" : (pct >= 50 ? "#f5a623" : "#e53935");
  const C = 2 * Math.PI * 54;
  $("r-donut").innerHTML = '<svg width="140" height="140" viewBox="0 0 140 140">' +
    '<circle cx="70" cy="70" r="54" fill="none" stroke="rgba(128,128,128,.25)" stroke-width="14"/>' +
    '<circle cx="70" cy="70" r="54" fill="none" stroke="' + col + '" stroke-width="14" stroke-linecap="round" ' +
    'stroke-dasharray="' + C.toFixed(1) + '" stroke-dashoffset="' + C.toFixed(1) + '"/></svg>' +
    '<b style="color:' + col + '">' + pct + '%</b>';
  setTimeout(() => {
    const arc = $("r-donut").querySelectorAll("circle")[1];
    if (arc) { arc.style.transition = "stroke-dashoffset 1s ease"; arc.style.strokeDashoffset = (C * (1 - pct / 100)).toFixed(1); }
  }, 60);
  $("r-main").textContent = r.correct + "/" + r.total;
  $("r-pen").textContent = "-" + r.penalties;
  $("r-score").textContent = r.score;
  const w = $("r-wrong"); w.innerHTML = "";
  if (!r.wrong.length) { w.textContent = "🎉 Xatosiz!"; }
  r.wrong.forEach(x => {
    const d = document.createElement("div"); d.className = "wrong";
    d.textContent = x.q + ") siz: " + (x.given ? x.given.toUpperCase() : "—") + " → to'g'ri: " + x.right.toUpperCase();
    w.appendChild(d);
  });
  show("res");
  if (pct >= 80 && !r.kicked) { confetti(); haptic("success"); }
}

async function submit(auto) {
  if (finished) return;
  const go = async () => {
    try { const r = await api("/api/submit"); showResult(r.result); }
    catch (e) { toast(e.message); }
  };
  if (auto) return go();
  ignoreAway = true;
  const total = S.questions ? S.questions.length : 0;
  const rest = total - Object.keys(answers).length;
  const msg = (rest > 0 ? rest + " ta savolga javob berilmagan. " : "") + "Testni yakunlaysizmi? Keyin o'zgartirib bo'lmaydi.";
  tg.showConfirm(msg, ok => {
    ignoreAway = false;
    if (ok) go();
  });
}
$("finish").onclick = () => submit(false);

/* ---- Savol-savol rejimi ---- */
let cur = 0, QD = {};
function isQuiz() { return !!(S && S.kind === "quiz" && S.qdata && S.qdata.length); }
function qItem(q) {
  const it = QD[q];
  if (it) return it;
  const o = {}; (S.options || ["a", "b", "c", "d"]).forEach(l => { o[l] = ""; });
  return {q: q, t: "", o: o};
}
function optEl(tag, l, txt, cls) {
  const d = document.createElement(tag); d.className = "opt" + (cls ? " " + cls : "");
  const c = document.createElement("span"); c.className = "ol"; c.textContent = l.toUpperCase();
  const t = document.createElement("span"); t.className = "ot"; t.textContent = txt;
  d.appendChild(c); d.appendChild(t);
  return d;
}
function hashStr(str) {
  let h = 1779033703 ^ str.length;
  for (let i = 0; i < str.length; i++) { h = Math.imul(h ^ str.charCodeAt(i), 3432918353); h = (h << 13) | (h >>> 19); }
  return h >>> 0;
}
function mulberry32(a) {
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
function shuffleArr(arr, rnd) {
  for (let i = arr.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); const t = arr[i]; arr[i] = arr[j]; arr[j] = t; }
  return arr;
}
function prepOrder() {
  const mode = S.shuffle || 0, rnd = mulberry32(hashStr(String(S.seed || CODE)));
  SEQ = S.questions.slice(); PERM = {};
  if (mode >= 1) shuffleArr(SEQ, rnd);
  S.questions.forEach(q => {
    const letters = Object.keys(qItem(q).o);
    PERM[q] = mode >= 2 ? shuffleArr(letters.slice(), rnd) : letters;
  });
}
function applyFs() { document.documentElement.style.setProperty("--fs", fs + "px"); }
function go(i) { if (i < 0 || i >= SEQ.length) return; cur = i; renderQuiz(true); window.scrollTo(0, 0); }
function buildQuiz() {
  QD = {}; S.qdata.forEach(x => { QD[x.q] = x; });
  prepOrder();
  const U = (tg.initDataUnsafe && tg.initDataUnsafe.user) || {};
  $("q-user").textContent = "👤 " + ((U.first_name || "") + " " + (U.last_name || "")).trim();
  $("q-id").textContent = U.id ? ("ID: " + U.id) : "";
  $("q-title").textContent = S.title;
  flagKey = "fl:" + CODE + ":" + (U.id || "");
  try { flags = JSON.parse(lsGet(flagKey) || "{}") || {}; } catch (e) { flags = {}; }
  fs = parseInt(lsGet("fs") || "18", 10) || 18; applyFs();
  const first = SEQ.findIndex(n => !answers[n]);
  cur = first >= 0 ? first : 0;
  $("q-prev").onclick = () => go(cur - 1);
  $("q-next").onclick = () => { if (cur < SEQ.length - 1) go(cur + 1); else submit(false); };
  $("q-finish").onclick = () => submit(false);
  $("t-small").onclick = () => { fs = Math.max(14, fs - 2); lsSet("fs", String(fs)); applyFs(); };
  $("t-big").onclick = () => { fs = Math.min(26, fs + 2); lsSet("fs", String(fs)); applyFs(); };
  $("t-flag").onclick = () => {
    const q = SEQ[cur];
    if (flags[q]) delete flags[q]; else flags[q] = 1;
    lsSet(flagKey, JSON.stringify(flags)); renderQuiz();
  };
  renderQuiz(true);
}
function renderQuiz(anim) {
  const q = SEQ[cur], item = qItem(q);
  $("q-num").textContent = (cur + 1) + "-savol / " + SEQ.length;
  $("q-text").textContent = item.t;
  if (anim) { const c = $("q-card"); c.classList.remove("slide"); void c.offsetWidth; c.classList.add("slide"); }
  const box = $("q-opts"); box.innerHTML = "";
  PERM[q].forEach((l, i) => {
    const b = optEl("button", String.fromCharCode(97 + i), item.o[l], answers[q] === l ? "sel" : "");
    b.onclick = () => choose(l);
    box.appendChild(b);
  });
  $("t-flag").classList.toggle("on", !!flags[q]);
  $("q-prev").disabled = cur === 0;
  $("q-next").textContent = cur === SEQ.length - 1 ? "Yakunlash" : "Keyingi";
  const g = $("q-grid"); g.innerHTML = "";
  SEQ.forEach((n, i) => {
    const b = document.createElement("button");
    b.className = "gn" + (answers[n] ? " done" : "") + (i === cur ? " cur" : "") + (flags[n] ? " flag" : "");
    b.textContent = i + 1;
    b.onclick = () => go(i);
    g.appendChild(b);
  });
  const done = Object.keys(answers).length, all = done === SEQ.length;
  $("q-count").textContent = done + " / " + SEQ.length;
  $("q-bar").style.width = (done / SEQ.length * 100) + "%";
  $("q-allmsg").classList.toggle("hidden", !all);
  $("q-finish").classList.toggle("pulse", all);
  if (all && !allShown) { allShown = true; haptic("success"); }
  if (!all) allShown = false;
}
function choose(l) {
  const q = SEQ[cur];
  const nv = answers[q] === l ? "" : l;
  if (nv) answers[q] = nv; else delete answers[q];
  renderQuiz();
  api("/api/answer", {q: q, a: nv}).catch(e => {
    if (String(e.message).indexOf("expired") >= 0) submit(true);
    else toast("Javob saqlanmadi, qayta bosing");
  });
}
function renderReviewQuiz(onlyWrong) {
  const box = $("rv-ans"); box.innerHTML = ""; box.className = "qwrap";
  const byQ = {}; (RES.items || RES.wrong || []).forEach(x => { byQ[x.q] = x; });
  let shown = 0;
  SEQ.forEach((q, i) => {
    const x = byQ[q];
    if (!x) return;
    const ok = x.given === x.right;
    if (onlyWrong && ok) return;
    const item = qItem(q);
    shown++;
    const card = document.createElement("div"); card.className = "qcard"; card.style.marginBottom = "14px";
    const n = document.createElement("div"); n.className = "qnum"; n.textContent = (i + 1) + "-savol  " + (ok ? "✅" : "❌");
    const t = document.createElement("div"); t.className = "qtext"; t.textContent = item.t;
    card.appendChild(n); card.appendChild(t);
    PERM[q].forEach((l, k) => {
      card.appendChild(optEl("div", String.fromCharCode(97 + k), item.o[l], l === x.right ? "good" : (l === x.given ? "bad" : "")));
    });
    if (!x.given) {
      const m = document.createElement("div"); m.style.color = "#8a8fb0"; m.textContent = "Javob berilmagan";
      card.appendChild(m);
    }
    box.appendChild(card);
  });
  if (!shown) {
    const d = document.createElement("div"); d.className = "center"; d.textContent = onlyWrong ? "🎉 Xato yo'q" : "Ma'lumot yo'q";
    box.appendChild(d);
  }
}

/* ---- Xatolar tahlili ---- */
function openReview() {
  if (isQuiz()) {
    if (!SEQ.length) { QD = {}; S.qdata.forEach(x => { QD[x.q] = x; }); prepOrder(); }
    $("rt-ans").textContent = "📋 Hammasi"; $("rt-doc").textContent = "⚠️ Faqat xatolar";
    show("rev"); setRevTab("ans"); return;
  }
  const box = $("rv-ans"); box.innerHTML = "";
  const items = RES.items || RES.wrong;
  items.forEach(x => {
    const ok = x.given === x.right;
    const row = document.createElement("div"); row.className = "q" + (ok ? "" : " bad");
    const n = document.createElement("b"); n.textContent = x.q + ".";
    const t = document.createElement("div"); t.style.flex = "1";
    t.textContent = (ok ? "✅ " : "❌ ") + "Siz: " + (x.given ? x.given.toUpperCase() : "—") +
      (ok ? "" : "   →   To'g'ri: " + x.right.toUpperCase());
    row.appendChild(n); row.appendChild(t); box.appendChild(row);
  });
  show("rev"); setRevTab("ans");
}
function setRevTab(t) {
  if (isQuiz()) {
    $("rv-doc").classList.add("hidden"); $("rv-ans").classList.remove("hidden");
    $("rt-ans").classList.toggle("on", t === "ans"); $("rt-doc").classList.toggle("on", t === "doc");
    renderReviewQuiz(t === "doc"); window.scrollTo(0, 0); return;
  }
  $("rv-ans").classList.toggle("hidden", t !== "ans");
  $("rv-doc").classList.toggle("hidden", t !== "doc");
  $("rt-ans").classList.toggle("on", t === "ans");
  $("rt-doc").classList.toggle("on", t === "doc");
  if (t === "doc" && !revDocLoaded) { revDocLoaded = true; loadDoc($("doc2")); }
  window.scrollTo(0, 0);
}
$("revbtn").onclick = openReview;
$("rev-back").onclick = () => show("res");
$("rt-ans").onclick = () => setRevTab("ans");
$("rt-doc").onclick = () => setRevTab("doc");
$("closebtn").onclick = () => tg.close();

/* ---- Ilovadan chiqishni aniqlash ---- */
function goAway(viaBeacon) {
  if (away || finished || ignoreAway || !S) return;
  away = true;
  if (viaBeacon && navigator.sendBeacon) {
    navigator.sendBeacon("/api/leave", new Blob([JSON.stringify({init: INIT, code: CODE})], {type: "application/json"}));
  } else {
    leaveP = post("/api/leave", {}, true).catch(() => {});
  }
}
async function comeBack() {
  if (!away || finished || !S) return;
  away = false;
  await Promise.race([leaveP, new Promise(r => setTimeout(r, 1500))]);
  try {
    const r = await api("/api/back");
    if (r.finished) { showResult(r.result); return; }
    endAt = Date.now() + r.left * 1000;
    setPen(r.penalties);
    if (r.penalized) toast("⚠️ Ilovadan chiqdingiz: -1 ball");
  } catch (e) {}
}
document.addEventListener("visibilitychange", () => { document.hidden ? goAway(false) : comeBack(); });
window.addEventListener("pagehide", () => goAway(true));
tg.onEvent("deactivated", () => goAway(false));
tg.onEvent("activated", comeBack);

/* ---- Boshlash ---- */
(async function init() {
  if (!INIT || !CODE) { fatal("Bu sahifani Telegram bot orqali oching."); return; }
  try { S = await api("/api/start"); } catch (e) { fatal(e.message); return; }
  if (S.finished) { showResult(S.result); return; }
  answers = S.answers || {};
  $("title").textContent = S.title;
  setPen(S.penalties);
  endAt = Date.now() + S.left * 1000;
  initialLeft = S.left;
  if (isQuiz()) { buildQuiz(); show("quiz"); } else { buildSheet(); show("test"); }
  tick(); setInterval(tick, 1000);
  setInterval(async () => {
    if (finished || away) return;
    try {
      const r = await api("/api/sync");
      if (r.finished) { showResult(r.result); return; }
      const prev = endAt;
      endAt = Date.now() + r.left * 1000;
      if (endAt - prev > 20000) toast("⏱ Test vaqti uzaytirildi");
    } catch (e) {}
  }, 15000);
  if (!isQuiz()) loadDoc();
})();
</script>
</body></html>
"""


# ----------------------------- BOT -----------------------------
class Create(StatesGroup):
    title = State()
    file = State()
    key = State()
    minutes = State()


class Join(StatesGroup):
    code = State()


router = Router()

menu_kb = ReplyKeyboardMarkup(
    keyboard=[
        [KeyboardButton(text="➕ Test yaratish"), KeyboardButton(text="✍️ Testni yechish")],
        [KeyboardButton(text="📊 Mening testlarim")],
    ],
    resize_keyboard=True,
)


KEY_PROMPT = (
    "🔑 <b>3/4-qadam</b>\nJavoblar kalitini yuboring.\n\n"
    "Misol: <code>abcdabcdab</code>\n"
    "yoki: <code>1a 2b 3c 4d</code>"
)


@router.message(CommandStart())
async def cmd_start(m: Message, state: FSMContext, command: CommandObject):
    await state.clear()
    if command.args:
        return await show_test(m, command.args.strip().upper())
    await m.answer(
        "👋 <b>Salom! Bu — test boti.</b>\n\n"
        "✍️ <b>Testni yechish</b> — kod yoki havola orqali\n"
        "➕ <b>Test yaratish</b> — o'z testingizni tuzib, kodni ulashing\n"
        "📊 <b>Mening testlarim</b> — natijalar va boshqaruv\n\n"
        "⚙️ Test egasi buyruqlari: /yordam",
        reply_markup=menu_kb,
    )


# ---------- Test yaratish ----------
@router.message(F.text == "➕ Test yaratish", StateFilter(None))
async def create_start(m: Message, state: FSMContext):
    await state.set_state(Create.title)
    await m.answer("📝 <b>1/4-qadam</b>\nTest nomini yuboring:")


@router.message(Create.title, F.text)
async def create_title(m: Message, state: FSMContext):
    await state.update_data(title=m.text.strip()[:100])
    await state.set_state(Create.file)
    await m.answer(
        "📎 <b>2/4-qadam</b>\n"
        "Test faylini yuboring (<b>PDF</b> yoki <b>.docx</b>)\n"
        "yoki testni <b>matn</b> qilib yozib yuboring (uzun bo'lsa, bir necha xabarga bo'lib).\n\n"
        "Matnni shu ko'rinishda yozsangiz, har bir savol variantlari bilan alohida sahifada chiqadi:\n"
        "<code>1. Savol matni\nA) variant\nB) variant\nC) variant\nD) variant</code>"
    )


@router.message(Create.file, F.document)
async def create_file_step(m: Message, state: FSMContext, bot: Bot):
    doc = m.document
    name = (doc.file_name or "").lower()
    mime = doc.mime_type or ""
    if mime == "application/pdf" or name.endswith(".pdf"):
        kind = "pdf"
    elif mime == DOCX_MIME or name.endswith(".docx"):
        kind = "docx"
    else:
        return await m.answer(
            "❌ Faqat PDF yoki .docx qabul qilinadi.\n"
            "Eski .doc bo'lsa, Word'da «Saqlash» orqali .docx qilib saqlang."
        )
    if doc.file_size and doc.file_size > 19 * 1024 * 1024:
        return await m.answer("❌ Fayl 19 MB dan katta bo'lmasligi kerak.")
    if kind == "docx":  # Word ichidan savol-variantlarni ajratib ko'ramiz
        qs = None
        try:
            buf = io.BytesIO()
            await bot.download(doc.file_id, destination=buf)
            text = docx_to_text(buf.getvalue())
            qs = parse_quiz(text) if text else None
        except Exception:
            text = None
        if qs:
            await state.update_data(
                file_id=doc.file_id, kind="quiz", body=text, questions=json.dumps(qs, ensure_ascii=False)
            )
            await state.set_state(Create.key)
            return await m.answer(
                "📄 Word fayldan savollar o'qildi.\n" + quiz_note(qs) + "\nHar biri alohida sahifada ko'rsatiladi.\n\n" + KEY_PROMPT
            )
        await m.answer(
            "ℹ️ Word fayldan savollarni ajratib bo'lmadi (raqam va harflar avtomatik ro'yxat bo'lishi mumkin). "
            "Fayl o'z holicha ko'rsatiladi."
        )
    await state.update_data(file_id=doc.file_id, kind=kind)
    await state.set_state(Create.key)
    await m.answer(KEY_PROMPT)


@router.message(Create.file, F.text)
async def create_text_part(m: Message, state: FSMContext):
    data = await state.get_data()
    parts = data.get("parts", [])
    parts.append(m.text)
    total = sum(len(x) for x in parts)
    if total > 60000:
        return await m.answer("❌ Matn juda uzun (60 000 belgidan oshmasin).")
    await state.update_data(parts=parts)
    kb = InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="✅ Tayyor", callback_data="text_done")]]
    )
    await m.answer(
        f"📝 {len(parts)}-qism qabul qilindi (jami {total} belgi).\n"
        "Yana matn yuborsangiz, davomiga qo'shiladi. Tugagach «✅ Tayyor» ni bosing.",
        reply_markup=kb,
    )


@router.callback_query(F.data == "text_done", Create.file)
async def text_done(c: CallbackQuery, state: FSMContext):
    data = await state.get_data()
    parts = data.get("parts", [])
    if not parts:
        return await c.answer("Avval matn yuboring", show_alert=True)
    body = "\n".join(parts)
    qs = parse_quiz(body)
    if qs:
        await state.update_data(
            kind="quiz", body=body, file_id="", questions=json.dumps(qs, ensure_ascii=False)
        )
        sizes = [len(q["o"]) for q in qs]
        common = max(set(sizes), key=sizes.count)
        odd = [str(q["q"]) for q in qs if len(q["o"]) != common]
        note = (
            f"\n⚠️ Variantlar soni {common} tadan farq qiladigan savollar: {', '.join(odd[:20])}. Tekshirib ko'ring."
            if odd else ""
        )
        await c.message.answer(
            f"✅ {len(qs)} ta savol, har birida {common} tadan variant aniqlandi. "
            f"Har biri alohida sahifada ko'rsatiladi.{note}"
        )
    else:
        await state.update_data(kind="text", body=body, file_id="", questions=None)
        await c.message.answer(
            "ℹ️ Savol va variantlar (1. ... A) ...) formatida aniqlanmadi, matn oddiy ko'rinishda ko'rsatiladi."
        )
    await state.set_state(Create.key)
    await c.message.answer(KEY_PROMPT)
    await c.answer()


@router.message(Create.file)
async def create_file_wrong(m: Message):
    await m.answer("Iltimos, fayl (PDF yoki .docx) yoki oddiy matn yuboring.")


@router.message(Create.key, F.text)
async def create_key(m: Message, state: FSMContext):
    key = parse_answers(m.text)
    if not key:
        return await m.answer("❌ Javoblar topilmadi. Qayta yuboring (masalan: abcdabcd).")
    data = await state.get_data()
    if data.get("questions"):
        qs = json.loads(data["questions"])
        if set(key.keys()) != {q["q"] for q in qs}:
            return await m.answer(
                f"⚠️ Matnda {len(qs)} ta savol bor, kalitda esa {len(key)} ta javob. Kalitni qayta yuboring."
            )
        for q in qs:
            if key[q["q"]] not in q["o"]:
                return await m.answer(
                    f"⚠️ {q['q']}-savolda «{key[q['q']].upper()}» varianti yo'q. Kalitni qayta yuboring."
                )
    await state.update_data(key=encode_key(key))
    await state.set_state(Create.minutes)
    await m.answer(f"✅ {len(key)} ta javob qabul qilindi.\n\n⏱ <b>4/4-qadam</b>\nTest necha daqiqa davom etadi? (raqam)")


@router.message(Create.minutes, F.text)
async def create_minutes(m: Message, state: FSMContext, bot: Bot):
    if not m.text.strip().isdigit() or not (1 <= int(m.text) <= 600):
        return await m.answer("1 dan 600 gacha raqam yuboring.")
    data = await state.get_data()
    code = new_code()
    db.execute(
        "INSERT INTO tests(code,owner_id,title,file_id,kind,answer_key,minutes,created,body,questions) "
        "VALUES(?,?,?,?,?,?,?,?,?,?)",
        (code, m.from_user.id, data["title"], data["file_id"], data["kind"],
         data["key"], int(m.text), time.time(), data.get("body"), data.get("questions")),
    )
    db.commit()
    await state.clear()
    me = await bot.get_me()
    nq = len(decode_key(data["key"]))
    await m.answer(
        f"🎉 <b>Test tayyor!</b>\n\n"
        f"📌 Nomi: {html.escape(data['title'])}\n"
        f"🔑 Kod: <code>{code}</code>\n"
        f"❓ Savollar: {nq} ta\n"
        f"⏱ Vaqt: {m.text} daqiqa\n\n"
        f"🔗 Havola: https://t.me/{me.username}?start={code}\n\n"
        f"⚙️ Boshqarish buyruqlari: /yordam",
        reply_markup=menu_kb,
    )


# ---------- Testni yechish ----------
@router.message(F.text == "✍️ Testni yechish", StateFilter(None))
async def join_start(m: Message, state: FSMContext):
    await state.set_state(Join.code)
    await m.answer("Test kodini kiriting:")


@router.message(Join.code, F.text)
async def join_code(m: Message, state: FSMContext):
    await state.clear()
    await show_test(m, m.text.strip().upper())


async def show_test(m: Message, code: str):
    test = get_test(code)
    if not test:
        return await m.answer("❌ Bunday kodli test topilmadi.", reply_markup=menu_kb)
    uid = m.from_user.id
    att = get_attempt(code, uid)
    if att and att["finished"]:
        res, _ = finalize(code, uid)
        return await m.answer(
            "Siz bu testni allaqachon yechib bo'lgansiz.\n\n" + result_text(res),
            reply_markup=review_kb(code),
        )
    if not att:
        block = start_block(test, uid)
        if block:
            return await m.answer(block, reply_markup=menu_kb)
    if not WEBAPP_URL:
        return await m.answer("⚠️ WEBAPP_URL sozlanmagan. Bot egasiga xabar bering.")
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="📝 Testni ochish", web_app=WebAppInfo(url=f"{WEBAPP_URL}/app?code={code}"))]
        ]
    )
    status = "Davom ettirish uchun tugmani bosing." if att else "Tugmani bosganingizda vaqt boshlanadi."
    nq = len(decode_key(test["answer_key"]))
    await m.answer(
        f"📝 <b>{html.escape(test['title'])}</b>\n\n"
        f"❓ Savollar: {nq} ta\n"
        f"⏱ Vaqt: {test['minutes']} daqiqa\n"
        f"⚠️ Ilovadan chiqsangiz -1 ball ayriladi\n\n{status}",
        reply_markup=kb,
    )


# ---------- Vaqtni uzaytirish (test egasi) ----------
@router.message(Command("vaqt"))
async def add_time(m: Message, command: CommandObject, bot: Bot):
    args = (command.args or "").split()
    if len(args) != 2 or not re.fullmatch(r"\d{1,3}", args[1]):
        return await m.answer("Ishlatish: /vaqt KOD DAQIQA\nMasalan: <code>/vaqt AB12CD 5</code>")
    code, add = args[0].upper(), int(args[1])
    test = get_test(code)
    if not test or test["owner_id"] != m.from_user.id:
        return await m.answer("Test topilmadi yoki u sizniki emas.")
    if not 1 <= add <= 180:
        return await m.answer("1 dan 180 daqiqagacha kiriting.")
    db.execute("UPDATE tests SET minutes=minutes+? WHERE code=?", (add, code))
    db.commit()
    rows = db.execute(
        "SELECT user_id FROM attempts WHERE code=? AND finished=0", (code,)
    ).fetchall()
    for r in rows:
        try:
            await bot.send_message(r["user_id"], f"⏱ Test vaqti {add} daqiqaga uzaytirildi.")
        except Exception:
            pass
    await m.answer(
        f"✅ {add} daqiqa qo'shildi. Yangi umumiy vaqt: {test['minutes'] + add} daqiqa.\n"
        f"Hozir yechayotganlar: {len(rows)} ta."
    )


# ---------- Yechayotganlar va chiqarish (test egasi) ----------
PRESENCE_SEC = 45  # shuncha soniya signal bo'lmasa "aloqa yo'q"
MAX_SHOWN = 30


def owner_test(code, uid):
    t = get_test(code)
    return t if t and t["owner_id"] == uid else None


def fmt_left(sec: float) -> str:
    sec = max(0, int(sec))
    h, r = divmod(sec, 3600)
    mi, se = divmod(r, 60)
    return f"{h}:{mi:02d}:{se:02d}" if h else f"{mi:02d}:{se:02d}"


def active_view(code: str, note: str = ""):
    test = get_test(code)
    rows = db.execute(
        "SELECT * FROM attempts WHERE code=? AND finished=0 ORDER BY started", (code,)
    ).fetchall()
    total = len(decode_key(test["answer_key"]))
    now = time.time()
    lines, kb = [], []
    for r in rows[:MAX_SHOWN]:
        name = r["name"] or str(r["user_id"])
        done = len(json.loads(r["answers"] or "{}"))
        if r["left_at"]:
            st = "🔴 ilovadan chiqqan"
        elif r["last_seen"] and now - r["last_seen"] <= PRESENCE_SEC:
            st = "🟢 ilovada"
        else:
            st = "⚪️ aloqa yo'q"
        pen = f" | jarima -{r['penalties'] * PENALTY}" if r["penalties"] else ""
        lines.append(
            f"• <b>{html.escape(name)}</b> — {st}\n"
            f"   ⏱ {fmt_left(time_left(test, r))} | ✍️ {done}/{total}{pen}"
        )
        kb.append([InlineKeyboardButton(text=f"❌ {name[:24]}", callback_data=f"kick:{code}:{r['user_id']}")])
    if len(rows) > MAX_SHOWN:
        lines.append(f"... va yana {len(rows) - MAX_SHOWN} ta")
    head = f"👥 <b>{html.escape(test['title'])}</b> ({code})\nHozir yechayotganlar: {len(rows)} ta\n\n"
    body = "\n".join(lines) if lines else "Hozir hech kim yechmayapti."
    kb.append([InlineKeyboardButton(text="🔄 Yangilash", callback_data=f"act:{code}")])
    return note + head + body, InlineKeyboardMarkup(inline_keyboard=kb)


@router.message(Command("yechayotganlar"))
async def active_cmd(m: Message, command: CommandObject):
    code = (command.args or "").strip().upper()
    if not code:
        mine = db.execute("SELECT code, title FROM tests WHERE owner_id=?", (m.from_user.id,)).fetchall()
        if not mine:
            return await m.answer("Sizda hali test yo'q.")
        if len(mine) > 1:
            lst = "\n".join(f"• {html.escape(t['title'])} — <code>{t['code']}</code>" for t in mine)
            return await m.answer("Qaysi test? Masalan: <code>/yechayotganlar KOD</code>\n\n" + lst)
        code = mine[0]["code"]
    if not owner_test(code, m.from_user.id):
        return await m.answer("Test topilmadi yoki u sizniki emas.")
    text, kb = active_view(code)
    await m.answer(text, reply_markup=kb)


async def _show_active(c: CallbackQuery, code: str, note: str = ""):
    text, kb = active_view(code, note)
    try:
        await c.message.edit_text(text, reply_markup=kb)
    except TelegramBadRequest:
        pass  # matn o'zgarmagan


@router.callback_query(F.data.startswith("act:"))
async def act_cb(c: CallbackQuery):
    code = c.data.split(":", 1)[1]
    if not owner_test(code, c.from_user.id):
        return await c.answer("Ruxsat yo'q", show_alert=True)
    await _show_active(c, code)
    await c.answer("Yangilandi")


@router.callback_query(F.data.startswith("kick:"))
async def kick_cb(c: CallbackQuery):
    _, code, uid = c.data.split(":")
    uid = int(uid)
    if not owner_test(code, c.from_user.id):
        return await c.answer("Ruxsat yo'q", show_alert=True)
    att = get_attempt(code, uid)
    if not att or att["finished"]:
        await c.answer("Bu odam allaqachon tugatgan", show_alert=True)
        return await _show_active(c, code)
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="✅ Ha, chiqarish", callback_data=f"kickok:{code}:{uid}"),
                InlineKeyboardButton(text="↩️ Bekor", callback_data=f"act:{code}"),
            ]
        ]
    )
    await c.message.edit_text(
        f"❌ <b>{html.escape(att['name'] or str(uid))}</b> ni testdan chiqarasizmi?\n\n"
        "Natijasi hozirgacha bergan javoblari bo'yicha hisoblanadi.",
        reply_markup=kb,
    )
    await c.answer()


@router.callback_query(F.data.startswith("kickok:"))
async def kickok_cb(c: CallbackQuery, bot: Bot):
    _, code, uid = c.data.split(":")
    uid = int(uid)
    if not owner_test(code, c.from_user.id):
        return await c.answer("Ruxsat yo'q", show_alert=True)
    att = get_attempt(code, uid)
    if not att or att["finished"]:
        await c.answer("Bu odam allaqachon tugatgan", show_alert=True)
        return await _show_active(c, code)
    name = att["name"] or str(uid)
    await conclude(
        bot, code, uid,
        "🚫 Test egasi sizni testdan chiqardi. Natijangiz hozirgacha bergan javoblaringiz bo'yicha hisoblandi.\n\n",
        kicked=True,
    )
    await _show_active(c, code, f"✅ {html.escape(name)} testdan chiqarildi.\n\n")
    await c.answer("Chiqarildi")


# ---------- Natijalar (test egasi) ----------
@router.message(F.text == "📊 Mening testlarim", StateFilter(None))
async def my_tests(m: Message):
    rows = db.execute("SELECT * FROM tests WHERE owner_id=?", (m.from_user.id,)).fetchall()
    if not rows:
        return await m.answer("Sizda hali test yo'q.")
    lines = [
        f"• {html.escape(r['title'])}{' 🔒' if r['closed'] else ''} — <code>{r['code']}</code>\n"
        f"   /natijalar {r['code']} · /yechayotganlar {r['code']}"
        for r in rows
    ]
    await m.answer("📚 <b>Testlaringiz:</b>\n\n" + "\n".join(lines) + "\n\n⚙️ Boshqa buyruqlar: /yordam")


@router.message(Command("natijalar"))
async def results(m: Message, command: CommandObject):
    code = (command.args or "").strip().upper()
    test = get_test(code)
    if not test or test["owner_id"] != m.from_user.id:
        return await m.answer("Test topilmadi yoki u sizniki emas.")
    rows = db.execute(
        "SELECT * FROM attempts WHERE code=? ORDER BY finished DESC, score DESC", (code,)
    ).fetchall()
    if not rows:
        return await m.answer("Hali hech kim yechmagan.")
    lines = []
    for i, r in enumerate(rows, 1):
        st = (
            f"{r['correct']}/{r['total']}, jarima -{r['penalties'] * PENALTY}, ball {r['score']}"
            + (" (chiqarilgan)" if r["result"] and json.loads(r["result"]).get("kicked") else "")
            if r["finished"] else "yechmoqda..."
        )
        lines.append(f"{i}. {html.escape(r['name'] or '')} — {st}")
    await m.answer(f"📊 <b>{html.escape(test['title'])}</b>\n\n" + "\n".join(lines))


# ---------- Test egasi: boshqaruv buyruqlari ----------
HELP_TEXT = (
    "⚙️ <b>Test egasi buyruqlari</b>\n\n"
    "👥 /yechayotganlar KOD — hozir kim yechayotgani, chiqarish\n"
    "📊 /natijalar KOD — barcha natijalar\n"
    "🏆 /reyting KOD — eng yaxshi natijalar\n"
    "📉 /tahlil KOD — eng ko'p xato qilingan savollar\n"
    "📥 /eksport KOD — natijalarni Excel (CSV) fayl qilib olish\n"
    "⏱ /vaqt KOD DAQIQA — vaqt qo'shish\n"
    "🔒 /yopish KOD — yangi yechuvchilarni to'xtatish\n"
    "🔓 /ochish KOD — qayta ochish\n"
    "🗓 /jadval KOD 20.11 20:00 21:00 — ochiq turish vaqti (o'chirish: /jadval KOD off)\n"
    "🔀 /aralash KOD 0|1|2 — 0: o'chiq, 1: savollar, 2: savollar va variantlar\n"
    "🔁 /qayta KOD — kimgadir qayta yechishga ruxsat\n"
    "📄 /nusxa KOD — testdan yangi kodli nusxa"
)


@router.message(Command("yordam"))
async def help_cmd(m: Message):
    await m.answer(HELP_TEXT)


async def own_test(m: Message, command: CommandObject, usage: str, min_args: int = 1):
    """Buyruq argumentlarini tekshiradi. (kod, test, qolgan_argumentlar) yoki None."""
    args = (command.args or "").split()
    if len(args) < min_args:
        await m.answer("Ishlatish: <code>" + usage + "</code>")
        return None
    code = args[0].upper()
    test = owner_test(code, m.from_user.id)
    if not test:
        await m.answer("Test topilmadi yoki u sizniki emas.")
        return None
    return code, test, args[1:]


def csv_safe(v) -> str:
    v = "" if v is None else str(v)
    return "'" + v if v[:1] in ("=", "+", "-", "@") else v


@router.message(Command("eksport"))
async def export_cmd(m: Message, command: CommandObject):
    r = await own_test(m, command, "/eksport KOD")
    if not r:
        return
    code, test, _ = r
    rows = db.execute(
        "SELECT * FROM attempts WHERE code=? ORDER BY finished DESC, score DESC", (code,)
    ).fetchall()
    if not rows:
        return await m.answer("Hali hech kim yechmagan.")
    buf = io.StringIO()
    w = csv.writer(buf, delimiter=";")
    w.writerow(["№", "Ism", "To'g'ri", "Jami", "Foiz", "Jarima", "Ball", "Holat", "Boshlagan", "Tugatgan", "Sarflangan (daq)"])
    for i, a in enumerate(rows, 1):
        res = json.loads(a["result"]) if a["result"] else {}
        if a["finished"]:
            holat = "chiqarilgan" if res.get("kicked") else "tugatgan"
            pct = round(a["score"] / a["total"] * 100) if a["total"] else 0
            spent = round((a["finished_at"] - a["started"]) / 60, 1) if a["finished_at"] else ""
            row = [a["correct"], a["total"], pct, a["penalties"] * PENALTY, a["score"], holat,
                   fmt_dt(a["started"]), fmt_dt(a["finished_at"]) if a["finished_at"] else "", spent]
        else:
            row = ["", "", "", a["penalties"] * PENALTY, "", "yechmoqda", fmt_dt(a["started"]), "", ""]
        w.writerow([i, csv_safe(a["name"])] + row)
    data = ("\ufeff" + buf.getvalue()).encode("utf-8")
    await m.answer_document(
        BufferedInputFile(data, filename=f"{code}_natijalar.csv"),
        caption=f"📥 <b>{html.escape(test['title'])}</b>: {len(rows)} ta natija\n(Excel yoki Google Sheets'da oching)",
    )


@router.message(Command("reyting"))
async def rating_cmd(m: Message, command: CommandObject):
    r = await own_test(m, command, "/reyting KOD")
    if not r:
        return
    code, test, _ = r
    rows = db.execute(
        "SELECT * FROM attempts WHERE code=? AND finished=1 "
        "ORDER BY score DESC, COALESCE(finished_at, 1e18) ASC LIMIT 15",
        (code,),
    ).fetchall()
    if not rows:
        return await m.answer("Hali hech kim tugatmagan.")
    medals = ["🥇", "🥈", "🥉"]
    lines = []
    for i, a in enumerate(rows):
        pct = round(a["score"] / a["total"] * 100) if a["total"] else 0
        mark = medals[i] if i < 3 else f"{i + 1}."
        lines.append(f"{mark} {html.escape(a['name'] or '')} — <b>{a['score']}/{a['total']}</b> ({pct}%)")
    await m.answer(f"🏆 <b>{html.escape(test['title'])}</b> reytingi\n\n" + "\n".join(lines))


@router.message(Command("tahlil"))
async def hard_cmd(m: Message, command: CommandObject):
    r = await own_test(m, command, "/tahlil KOD")
    if not r:
        return
    code, test, _ = r
    rows = db.execute(
        "SELECT result FROM attempts WHERE code=? AND finished=1 AND result IS NOT NULL", (code,)
    ).fetchall()
    n = len(rows)
    if n == 0:
        return await m.answer("Hali hech kim tugatmagan.")
    cnt = Counter()
    for a in rows:
        for x in json.loads(a["result"]).get("wrong", []):
            cnt[x["q"]] += 1
    if not cnt:
        return await m.answer("🎉 Hamma barcha savollarga to'g'ri javob bergan.")
    qd = {x["q"]: x for x in (qdata_for(test) or [])}
    lines = []
    for q, c in cnt.most_common(10):
        line = f"<b>{q}-savol</b> — {round(c / n * 100)}% xato ({c}/{n})"
        if q in qd:
            line += f"\n   <i>{html.escape(qd[q]['t'][:60])}</i>"
        lines.append(line)
    await m.answer(
        f"📉 <b>{html.escape(test['title'])}</b>\nEng ko'p xato qilingan savollar ({n} kishi tugatgan):\n\n"
        + "\n".join(lines)
    )


async def _set_closed(m: Message, command: CommandObject, value: int):
    r = await own_test(m, command, "/yopish KOD" if value else "/ochish KOD")
    if not r:
        return
    code, test, _ = r
    db.execute("UPDATE tests SET closed=? WHERE code=?", (value, code))
    db.commit()
    await m.answer(
        f"🔒 <b>{html.escape(test['title'])}</b> yopildi. Yangi yechuvchilar kira olmaydi, "
        "boshlaganlar davom ettiradi." if value else
        f"🔓 <b>{html.escape(test['title'])}</b> qayta ochildi."
    )


@router.message(Command("yopish"))
async def close_cmd(m: Message, command: CommandObject):
    await _set_closed(m, command, 1)


@router.message(Command("ochish"))
async def open_cmd(m: Message, command: CommandObject):
    await _set_closed(m, command, 0)


@router.message(Command("nusxa"))
async def copy_cmd(m: Message, command: CommandObject, bot: Bot):
    r = await own_test(m, command, "/nusxa KOD")
    if not r:
        return
    code, test, _ = r
    new = new_code()
    db.execute(
        "INSERT INTO tests(code,owner_id,title,file_id,kind,answer_key,minutes,created,body,questions,shuffle) "
        "VALUES(?,?,?,?,?,?,?,?,?,?,?)",
        (new, test["owner_id"], (test["title"] + " (nusxa)")[:100], test["file_id"], test["kind"],
         test["answer_key"], test["minutes"], time.time(), test["body"], test["questions"], test["shuffle"] or 0),
    )
    db.commit()
    me = await bot.get_me()
    await m.answer(
        f"📄 Nusxa tayyor!\n\n🔑 Yangi kod: <code>{new}</code>\n"
        f"🔗 https://t.me/{me.username}?start={new}"
    )


def parse_local(day_month: str, hhmm: str):
    a = re.fullmatch(r"(\d{1,2})\.(\d{1,2})", day_month)
    b = re.fullmatch(r"(\d{1,2}):(\d{2})", hhmm)
    if not a or not b:
        return None
    year = time.gmtime(time.time() + TZ_OFFSET * 3600).tm_year
    try:
        dt = datetime.datetime(year, int(a.group(2)), int(a.group(1)), int(b.group(1)), int(b.group(2)),
                               tzinfo=datetime.timezone.utc)
    except ValueError:
        return None
    return dt.timestamp() - TZ_OFFSET * 3600


@router.message(Command("jadval"))
async def schedule_cmd(m: Message, command: CommandObject):
    usage = "/jadval KOD 20.11 20:00 21:00"
    r = await own_test(m, command, usage + "  (o'chirish: /jadval KOD off)", min_args=2)
    if not r:
        return
    code, test, rest = r
    if rest[0].lower() == "off":
        db.execute("UPDATE tests SET opens_at=NULL, closes_at=NULL WHERE code=?", (code,))
        db.commit()
        return await m.answer("🗓 Jadval o'chirildi. Test har doim ochiq.")
    if len(rest) != 3:
        return await m.answer("Ishlatish: <code>" + usage + "</code>")
    start, end = parse_local(rest[0], rest[1]), parse_local(rest[0], rest[2])
    if start is None or end is None or end <= start:
        return await m.answer("❌ Sana yoki vaqt noto'g'ri. Masalan: <code>" + usage + "</code>")
    db.execute("UPDATE tests SET opens_at=?, closes_at=? WHERE code=?", (start, end, code))
    db.commit()
    await m.answer(
        f"🗓 <b>{html.escape(test['title'])}</b>\nOchiladi: {fmt_dt(start)}\nYopiladi: {fmt_dt(end)}\n"
        f"(vaqt UTC+{TZ_OFFSET:g} bo'yicha). Yopilgandan keyin yangi yechuvchilar kira olmaydi."
    )


SHUFFLE_INFO = {"0": "o'chiq", "1": "savollar tartibi aralashadi", "2": "savollar va variantlar aralashadi"}


@router.message(Command("aralash"))
async def shuffle_cmd(m: Message, command: CommandObject):
    r = await own_test(m, command, "/aralash KOD 0|1|2", min_args=2)
    if not r:
        return
    code, test, rest = r
    if rest[0] not in SHUFFLE_INFO:
        return await m.answer("Ishlatish: <code>/aralash KOD 0|1|2</code>\n0 — o'chiq, 1 — savollar, 2 — savollar va variantlar")
    if test["kind"] != "quiz":
        return await m.answer("Aralashtirish faqat savol-savol ko'rinishidagi testlar uchun ishlaydi.")
    if db.execute("SELECT 1 FROM attempts WHERE code=? LIMIT 1", (code,)).fetchone():
        return await m.answer("Kimdir testni boshlab bo'lgan, endi o'zgartirib bo'lmaydi. /nusxa orqali yangi test oching.")
    db.execute("UPDATE tests SET shuffle=? WHERE code=?", (int(rest[0]), code))
    db.commit()
    await m.answer(f"🔀 Aralashtirish: {SHUFFLE_INFO[rest[0]]}.")


def retake_view(code: str, note: str = ""):
    test = get_test(code)
    rows = db.execute(
        "SELECT * FROM attempts WHERE code=? AND finished=1 ORDER BY COALESCE(finished_at, 0) DESC LIMIT 30",
        (code,),
    ).fetchall()
    kb = [
        [InlineKeyboardButton(
            text=f"🔁 {(a['name'] or str(a['user_id']))[:22]} — {a['score']}/{a['total']}",
            callback_data=f"retake:{code}:{a['user_id']}",
        )]
        for a in rows
    ]
    text = f"{note}🔁 <b>{html.escape(test['title'])}</b>\n"
    text += "Qayta yechishga ruxsat berish uchun ismni bosing:" if rows else "Hali hech kim tugatmagan."
    return text, InlineKeyboardMarkup(inline_keyboard=kb)


@router.message(Command("qayta"))
async def retake_cmd(m: Message, command: CommandObject):
    r = await own_test(m, command, "/qayta KOD")
    if not r:
        return
    text, kb = retake_view(r[0])
    await m.answer(text, reply_markup=kb)


@router.callback_query(F.data.startswith("retake:"))
async def retake_cb(c: CallbackQuery, bot: Bot):
    _, code, uid = c.data.split(":")
    uid = int(uid)
    test = owner_test(code, c.from_user.id)
    if not test:
        return await c.answer("Ruxsat yo'q", show_alert=True)
    att = get_attempt(code, uid)
    if not att or not att["finished"]:
        return await c.answer("Bu odam testni tugatmagan", show_alert=True)
    name = att["name"] or str(uid)
    db.execute(
        "INSERT INTO attempts_old(code,user_id,name,started,finished,correct,total,penalties,score,answers,"
        "left_at,result,last_seen,finished_at,archived) "
        "SELECT code,user_id,name,started,finished,correct,total,penalties,score,answers,"
        "left_at,result,last_seen,finished_at,? FROM attempts WHERE code=? AND user_id=?",
        (time.time(), code, uid),
    )
    db.execute("DELETE FROM attempts WHERE code=? AND user_id=?", (code, uid))
    db.commit()
    kb = None
    if WEBAPP_URL:
        kb = InlineKeyboardMarkup(
            inline_keyboard=[[InlineKeyboardButton(text="📝 Testni ochish", web_app=WebAppInfo(url=f"{WEBAPP_URL}/app?code={code}"))]]
        )
    try:
        await bot.send_message(
            uid,
            f"🔁 Test egasi sizga <b>{html.escape(test['title'])}</b> testini qayta yechishga ruxsat berdi.",
            reply_markup=kb,
        )
    except Exception:
        pass
    text, kb2 = retake_view(code, f"✅ {html.escape(name)} ga ruxsat berildi.\n\n")
    try:
        await c.message.edit_text(text, reply_markup=kb2)
    except TelegramBadRequest:
        pass
    await c.answer("Ruxsat berildi")


# ----------------------------- ISHGA TUSHIRISH -----------------------------
async def main():
    if not BOT_TOKEN:
        raise SystemExit("BOT_TOKEN o'rnatilmagan!")
    logging.basicConfig(level=logging.INFO)

    bot = Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)

    runner = web.AppRunner(make_web(bot))
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()
    logging.info("Veb-server ishga tushdi, port: %s | WEBAPP_URL: %s", PORT, WEBAPP_URL or "(yo'q)")

    resume_timers(bot)
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
