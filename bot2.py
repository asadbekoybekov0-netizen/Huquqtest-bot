"""
TEST BOT + MINI APP (aiogram 3.x + aiohttp)

Muhit o'zgaruvchilari (Railway -> Variables):
    BOT_TOKEN   - BotFather tokeni
    WEBAPP_URL  - Railway bergan https havola (oxirida / siz)
    DB_PATH     - (ixtiyoriy) baza fayli, masalan /data/tests2.db (Volume ulansa)
    PORT        - Railway o'zi beradi

Ishga tushirish:  python bot2.py
"""
import asyncio
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
from urllib.parse import parse_qsl

from aiohttp import web
from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandObject, CommandStart, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
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
    kind TEXT, answer_key TEXT, minutes INTEGER, created REAL, body TEXT, questions TEXT);
CREATE TABLE IF NOT EXISTS attempts(
    code TEXT, user_id INTEGER, name TEXT, started REAL,
    finished INTEGER DEFAULT 0, correct INTEGER DEFAULT 0, total INTEGER DEFAULT 0,
    penalties INTEGER DEFAULT 0, score INTEGER DEFAULT 0,
    answers TEXT DEFAULT '{}', left_at REAL, result TEXT,
    PRIMARY KEY(code, user_id));
"""
)


for _col in ("body", "questions"):  # eski bazalar uchun yangi ustunlar
    try:
        db.execute(f"ALTER TABLE tests ADD COLUMN {_col} TEXT")
        db.commit()
    except sqlite3.OperationalError:
        pass


def get_test(code):
    return db.execute("SELECT * FROM tests WHERE code=?", (code,)).fetchone()


def get_attempt(code, uid):
    return db.execute(
        "SELECT * FROM attempts WHERE code=? AND user_id=?", (code, uid)
    ).fetchone()


# ----------------------------- YORDAMCHI -----------------------------
def parse_answers(text: str) -> dict:
    """'abcd' yoki '1a 2b 3c' yoki '1-a,2-b' -> {raqam: harf}"""
    text = text.strip().lower()
    pairs = re.findall(r"(\d+)\s*[-.:)]*\s*([a-z])", text)
    if pairs:
        return {int(n): l for n, l in pairs}
    return {i + 1: l for i, l in enumerate(re.findall(r"[a-z]", text))}


Q_RE = re.compile(r"^\s*(\d{1,3})\s*[.)]\s*(.*\S.*)$")
O_RE = re.compile(r"^\s*\(?([A-Za-z])\)?\s*[).:]\s*(.*\S.*)$")


def parse_quiz(text: str):
    """'1. Savol / A) variant ...' matnini tuzilgan savollar ro'yxatiga aylantiradi."""
    qs, cur, last = [], None, None
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        mq = Q_RE.match(line)
        # yangi savol: raqami ketma-ket va oldingi savolda kamida 2 ta variant bor
        if mq and int(mq.group(1)) == len(qs) + 1 and (cur is None or len(cur["o"]) >= 2):
            cur = {"q": len(qs) + 1, "t": mq.group(2).strip(), "o": {}}
            qs.append(cur)
            last = "q"
            continue
        if cur is None:
            continue
        mo = O_RE.match(line)
        if mo:
            expect = chr(ord("a") + len(cur["o"]))
            if mo.group(1).lower() == expect:
                cur["o"][expect] = mo.group(2).strip()
                last = expect
                continue
        if last == "q":
            cur["t"] += "\n" + line
        elif last:
            cur["o"][last] += " " + line
    if not qs or any(len(q["o"]) < 2 for q in qs):
        return None
    return qs


def qdata_for(test):
    if test["kind"] != "quiz" or not test["questions"]:
        return None
    return json.loads(test["questions"])


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


def finalize(code: str, uid: int):
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
        "items": [
            {"q": n, "given": given.get(n, ""), "right": l}
            for n, l in sorted(key.items())
        ],
    }
    db.execute(
        "UPDATE attempts SET finished=1, correct=?, total=?, penalties=?, score=?, "
        "left_at=NULL, result=? WHERE code=? AND user_id=?",
        (correct, total, pen, score, json.dumps(res), code, uid),
    )
    db.commit()
    return res, True


def result_text(r: dict) -> str:
    t = (
        f"📊 <b>{html.escape(r['title'])}</b> natijasi\n\n"
        f"✅ To'g'ri: {r['correct']}/{r['total']}\n"
        f"🚪 Chiqib ketish jarimasi: -{r['penalties']}\n"
        f"🏆 Yakuniy ball: <b>{r['score']}</b>\n"
    )
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
        t += "\n🎉 Xatosiz!"
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


async def conclude(bot: Bot, code: str, uid: int, prefix: str = "") -> dict:
    res, new = finalize(code, uid)
    if new:
        try:
            await bot.send_message(uid, prefix + result_text(res), reply_markup=review_kb(code))
        except Exception:
            pass
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
        return web.json_response({"finished": True, "result": res, "kind": test["kind"], "qdata": qdata_for(test)})

    new = att is None
    if new:
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

    left = time_left(test, att)
    if left <= 0:
        res = await conclude(bot, code, uid, "⌛ Vaqt tugadi.\n\n")
        return web.json_response({"finished": True, "result": res, "kind": test["kind"], "qdata": qdata_for(test)})
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
<script src="https://telegram.org/js/telegram-web-app.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/pdf.js/3.11.174/pdf.min.js"></script>
<script src="https://cdnjs.cloudflare.com/ajax/libs/mammoth/1.6.0/mammoth.browser.min.js"></script>
<style>
:root{--bg:var(--tg-theme-bg-color,#fff);--tx:var(--tg-theme-text-color,#111);--hint:var(--tg-theme-hint-color,#888);--btn:var(--tg-theme-button-color,#2481cc);--btx:var(--tg-theme-button-text-color,#fff);--sec:var(--tg-theme-secondary-bg-color,#f1f1f1)}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--tx);font:16px/1.4 -apple-system,system-ui,sans-serif}
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
.qwrap{background:#f5f6fb;color:#151a4a;min-height:100vh;padding:14px 14px 40px}
.qhead{background:#161a4d;color:#fff;border-radius:16px;padding:12px 14px;display:flex;justify-content:space-between;gap:10px;font-size:14px;box-shadow:0 6px 16px rgba(22,26,77,.25)}
.qhead div{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.qrow{display:flex;justify-content:space-between;align-items:center;margin:14px 2px 6px;gap:10px}
.qtitle{font-weight:700;font-size:18px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;flex:1}
.qtimer{background:#fff;border:1px solid #e3e5f0;border-radius:999px;padding:8px 14px;font-weight:700;font-variant-numeric:tabular-nums;white-space:nowrap}
.qtimer.low{color:#e53935;border-color:#e53935}
.qwarn{font-size:13px;color:#8a8fb0;margin:0 2px 10px}
.qbar{height:8px;background:#e8eaf5;border-radius:99px;overflow:hidden;margin-bottom:14px}
.qbar i{display:block;height:100%;background:#5b67e8;border-radius:99px;width:0;transition:width .25s}
.qcard{background:#fff;border-radius:22px;padding:20px 16px;box-shadow:0 8px 24px rgba(30,36,100,.08)}
.qnum{color:#5b67e8;font-weight:600;font-size:14px;margin-bottom:8px}
.qtext{font-weight:700;font-size:18px;line-height:1.45;white-space:pre-wrap;word-wrap:break-word;margin-bottom:16px}
.opt{display:flex;align-items:center;gap:12px;width:100%;text-align:left;background:#fff;border:2px solid #e3e5f0;border-radius:18px;padding:12px 14px;margin-bottom:10px;font-size:16px;color:#151a4a;font-family:inherit}
.opt.sel{border-color:#5b67e8;background:#eef0ff}
.opt.good{border-color:#4db35a;background:#e8f7ea}
.opt.bad{border-color:#e53935;background:#fdeaea}
.ol{flex:none;width:34px;height:34px;border-radius:50%;background:#eceef8;display:flex;align-items:center;justify-content:center;font-weight:700;font-size:14px}
.opt.sel .ol{background:#5b67e8;color:#fff}
.opt.good .ol{background:#4db35a;color:#fff}
.opt.bad .ol{background:#e53935;color:#fff}
.ot{flex:1;white-space:pre-wrap;word-wrap:break-word}
.qnav{display:flex;justify-content:space-between;margin-top:14px}
.nbtn{padding:12px 22px;border-radius:999px;border:1px solid #e3e5f0;background:#fff;color:#151a4a;font-size:16px;font-weight:600}
.nbtn:disabled{opacity:.4}
.nbtn.pri{background:#5b67e8;color:#fff;border:0;box-shadow:0 8px 18px rgba(91,103,232,.35)}
.qgrid{display:grid;grid-template-columns:repeat(8,1fr);gap:8px;margin:18px 0 12px}
.gn{aspect-ratio:1;border-radius:12px;border:1px solid #e3e5f0;background:#fff;color:#151a4a;font-weight:600;font-size:14px;padding:0}
.gn.done{background:#5cc36a;border-color:#4db35a;color:#fff}
.gn.cur{background:#161a4d;border-color:#161a4d;color:#fff}
.qleg{font-size:13px;color:#6a6f94;display:flex;flex-wrap:wrap;gap:6px 14px;align-items:center}
.qleg i{display:inline-block;width:12px;height:12px;border-radius:4px;margin-right:4px;vertical-align:-1px}
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
  <div class="qcard">
    <div class="qnum" id="q-num"></div>
    <div class="qtext" id="q-text"></div>
    <div id="q-opts"></div>
    <div class="qnav"><button class="nbtn" id="q-prev">Oldingi</button><button class="nbtn pri" id="q-next">Keyingi</button></div>
  </div>
  <div class="qgrid" id="q-grid"></div>
  <div class="qleg"><b id="q-count"></b><span>javob berildi</span><span><i style="background:#5cc36a"></i>Javob berilgan</span><span><i style="background:#161a4d"></i>Hozirgi savol</span><span><i style="background:#fff;border:1px solid #e3e5f0"></i>Javobsiz</span></div>
  <div style="margin-top:18px"><button class="big" id="q-finish">✅ Testni yakunlash</button></div>
</div>

<div id="s-res" class="hidden">
  <div class="card">
    <h2 id="r-title"></h2>
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
try { if (tg.disableVerticalSwipes) tg.disableVerticalSwipes(); tg.enableClosingConfirmation(); } catch (e) {}
const INIT = tg.initData || "";
const CODE = (new URLSearchParams(location.search).get("code") || "").toUpperCase();
const $ = id => document.getElementById(id);
let S = null, finished = false, answers = {}, endAt = 0;
let away = false, ignoreAway = false, leaveP = Promise.resolve();

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
function buildQuiz() {
  QD = {}; S.qdata.forEach(x => { QD[x.q] = x; });
  const U = (tg.initDataUnsafe && tg.initDataUnsafe.user) || {};
  $("q-user").textContent = "👤 " + ((U.first_name || "") + " " + (U.last_name || "")).trim();
  $("q-id").textContent = U.id ? ("ID: " + U.id) : "";
  $("q-title").textContent = S.title;
  const first = S.questions.findIndex(n => !answers[n]);
  cur = first >= 0 ? first : 0;
  $("q-prev").onclick = () => { if (cur > 0) { cur--; renderQuiz(); window.scrollTo(0, 0); } };
  $("q-next").onclick = () => {
    if (cur < S.questions.length - 1) { cur++; renderQuiz(); window.scrollTo(0, 0); } else submit(false);
  };
  $("q-finish").onclick = () => submit(false);
  renderQuiz();
}
function renderQuiz() {
  const q = S.questions[cur], item = qItem(q);
  $("q-num").textContent = (cur + 1) + "-savol / " + S.questions.length;
  $("q-text").textContent = item.t;
  const box = $("q-opts"); box.innerHTML = "";
  Object.keys(item.o).forEach(l => {
    const b = optEl("button", l, item.o[l], answers[q] === l ? "sel" : "");
    b.onclick = () => choose(l);
    box.appendChild(b);
  });
  $("q-prev").disabled = cur === 0;
  $("q-next").textContent = cur === S.questions.length - 1 ? "Yakunlash" : "Keyingi";
  const g = $("q-grid"); g.innerHTML = "";
  S.questions.forEach((n, i) => {
    const b = document.createElement("button");
    b.className = "gn" + (answers[n] ? " done" : "") + (i === cur ? " cur" : "");
    b.textContent = n;
    b.onclick = () => { cur = i; renderQuiz(); window.scrollTo(0, 0); };
    g.appendChild(b);
  });
  const done = Object.keys(answers).length;
  $("q-count").textContent = done + " / " + S.questions.length;
  $("q-bar").style.width = (done / S.questions.length * 100) + "%";
}
function choose(l) {
  const q = S.questions[cur];
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
  let shown = 0;
  (RES.items || []).forEach(x => {
    const ok = x.given === x.right;
    if (onlyWrong && ok) return;
    const item = qItem(x.q);
    shown++;
    const card = document.createElement("div"); card.className = "qcard"; card.style.marginBottom = "14px";
    const n = document.createElement("div"); n.className = "qnum"; n.textContent = x.q + "-savol  " + (ok ? "✅" : "❌");
    const t = document.createElement("div"); t.className = "qtext"; t.textContent = item.t;
    card.appendChild(n); card.appendChild(t);
    Object.keys(item.o).forEach(l => {
      card.appendChild(optEl("div", l, item.o[l], l === x.right ? "good" : (l === x.given ? "bad" : "")));
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
    if (!Object.keys(QD).length) S.qdata.forEach(x => { QD[x.q] = x; });
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


@router.message(CommandStart())
async def cmd_start(m: Message, state: FSMContext, command: CommandObject):
    await state.clear()
    if command.args:
        return await show_test(m, command.args.strip().upper())
    await m.answer(
        "👋 Salom! Bu test boti.\n\n"
        "➕ Test yarating va kodni ulashing\n"
        "✍️ Yoki kod bilan testni yeching",
        reply_markup=menu_kb,
    )


# ---------- Test yaratish ----------
@router.message(F.text == "➕ Test yaratish", StateFilter(None))
async def create_start(m: Message, state: FSMContext):
    await state.set_state(Create.title)
    await m.answer("Test nomini yuboring:")


@router.message(Create.title, F.text)
async def create_title(m: Message, state: FSMContext):
    await state.update_data(title=m.text.strip()[:100])
    await state.set_state(Create.file)
    await m.answer(
        "Test faylini yuboring (<b>PDF</b> yoki <b>.docx</b>)\n"
        "yoki testni <b>matn</b> qilib yozib yuboring (uzun bo'lsa, bir necha xabarga bo'lib).\n\n"
        "Matnni shu ko'rinishda yozsangiz, har bir savol variantlari bilan alohida sahifada chiqadi:\n"
        "<code>1. Savol matni\nA) variant\nB) variant\nC) variant\nD) variant</code>"
    )


@router.message(Create.file, F.document)
async def create_file_step(m: Message, state: FSMContext):
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
    await state.update_data(file_id=doc.file_id, kind=kind)
    await state.set_state(Create.key)
    await m.answer(
        "Javoblar kalitini yuboring.\n\n"
        "Misol: <code>abcdabcdab</code>\n"
        "yoki: <code>1a 2b 3c 4d</code>"
    )


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
        await c.message.answer(
            f"✅ {len(qs)} ta savol variantlari bilan aniqlandi. Har biri alohida sahifada ko'rsatiladi."
        )
    else:
        await state.update_data(kind="text", body=body, file_id="", questions=None)
        await c.message.answer(
            "ℹ️ Savol va variantlar (1. ... A) ...) formatida aniqlanmadi, matn oddiy ko'rinishda ko'rsatiladi."
        )
    await state.set_state(Create.key)
    await c.message.answer(
        "Javoblar kalitini yuboring.\n\n"
        "Misol: <code>abcdabcdab</code>\n"
        "yoki: <code>1a 2b 3c 4d</code>"
    )
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
    await m.answer(f"✅ {len(key)} ta savol qabul qilindi.\n\n⏱ Test necha daqiqa davom etadi? (raqam)")


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
    await m.answer(
        f"🎉 Test tayyor!\n\n"
        f"📌 Nomi: {html.escape(data['title'])}\n"
        f"🔑 Kod: <code>{code}</code>\n"
        f"⏱ Vaqt: {m.text} daqiqa\n\n"
        f"Havola: https://t.me/{me.username}?start={code}\n"
        f"Natijalar: /natijalar {code}",
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
    if not WEBAPP_URL:
        return await m.answer("⚠️ WEBAPP_URL sozlanmagan. Bot egasiga xabar bering.")
    kb = InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="📝 Testni ochish", web_app=WebAppInfo(url=f"{WEBAPP_URL}/app?code={code}"))]
        ]
    )
    status = "Davom ettirish uchun tugmani bosing." if att else "Tugmani bosganingizda vaqt boshlanadi."
    await m.answer(
        f"📝 <b>{html.escape(test['title'])}</b>\n"
        f"⏱ {test['minutes']} daqiqa\n\n{status}\n"
        f"⚠️ Ilovadan chiqsangiz -1 ball ayriladi.",
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


# ---------- Natijalar (test egasi) ----------
@router.message(F.text == "📊 Mening testlarim", StateFilter(None))
async def my_tests(m: Message):
    rows = db.execute("SELECT * FROM tests WHERE owner_id=?", (m.from_user.id,)).fetchall()
    if not rows:
        return await m.answer("Sizda hali test yo'q.")
    lines = [f"• {html.escape(r['title'])} — <code>{r['code']}</code>  (/natijalar {r['code']})" for r in rows]
    await m.answer("📚 Testlaringiz:\n\n" + "\n".join(lines))


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
            if r["finished"] else "yechmoqda..."
        )
        lines.append(f"{i}. {html.escape(r['name'] or '')} — {st}")
    await m.answer(f"📊 <b>{html.escape(test['title'])}</b>\n\n" + "\n".join(lines))


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
