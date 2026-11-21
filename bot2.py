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
import unicodedata
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
    shuffle INTEGER DEFAULT 0, closed INTEGER DEFAULT 0, opens_at REAL, closes_at REAL,
    camera INTEGER DEFAULT 0, camera_secs INTEGER DEFAULT 7);
CREATE TABLE IF NOT EXISTS attempts(
    code TEXT, user_id INTEGER, name TEXT, started REAL,
    finished INTEGER DEFAULT 0, correct INTEGER DEFAULT 0, total INTEGER DEFAULT 0,
    penalties INTEGER DEFAULT 0, score INTEGER DEFAULT 0,
    answers TEXT DEFAULT '{}', left_at REAL, result TEXT, last_seen REAL, finished_at REAL, face_n INTEGER DEFAULT 0,
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
    ("tests", "camera INTEGER DEFAULT 0"),
    ("tests", "camera_secs INTEGER DEFAULT 7"),
    ("attempts", "face_n INTEGER DEFAULT 0"),
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


def camera_applies(test, uid) -> bool:
    """Kamera tekshiruvi shu yechuvchiga tegishlimi? 0: o'chiq, 1: hamma, 2: faqat test egasi (sinov)."""
    mode = test["camera"] or 0
    return mode == 1 or (mode == 2 and uid == test["owner_id"])


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


# Raqam belgisi (savol tartibi) yoki KATTA harf belgisi (variant): "7." / "№7." / "7-savol" / "A." / "B)" / "C,"
TOKEN_RE = re.compile(
    r"(?<!\d)(?:№\s*|#\s*)?(\d{1,3})\s*(?:[.)]|-\s*[Ss]avol\s*[.:)]?)(?!\d)"
    r"|(?<![A-Za-z0-9'ʻʼ’`])([A-J])\s*[.),]"
)
_PUNCT = str.maketrans({"）": ")", "．": ".", "。": ".", "：": ":", "，": ",", "․": ".", "﹒": ".", "‧": "."})
_LOOK = str.maketrans("АВСЕ", "ABCE")


def normalize_text(text: str) -> str:
    """Ko'rinmas belgilar, kirill-lotin o'xshash harflar va keng qavslarni tozalaydi."""
    t = text.replace("\r", "")
    t = t.replace("\u00a0", " ").replace("\u202f", " ").replace("\u2009", " ")
    t = re.sub(r"[\u200b-\u200f\u2060\ufeff\u00ad]", "", t)
    t = t.translate(_PUNCT)
    # variant belgisi o'rnidagi kirill А, В, С, Е ("А)" "В." ...) lotinchaga o'giriladi
    t = re.sub(r"(?<![\w'ʻʼ’])([АВСЕ])(?=\s*[.),])", lambda m: m.group(1).translate(_LOOK), t)
    return t


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


def _scan(t: str, first=None, gap: int = 0):
    """
    Matnni savollarga bo'ladi. first — birinchi savol raqami (standart 1).
    gap=0: raqamlar qat'iy ketma-ket; gap>0: orada raqam tushib qolgan bo'lsa ham qabul qilinadi.
    Yangi savol faqat oldingi savolda kamida 2 ta variant bo'lgandan keyin boshlanadi.
    """
    qs, cur, last = [], None, None
    kind, start = None, 0

    def close(end):
        chunk = t[start:end]
        if kind == "q":
            cur["t"] = _clean(chunk, keep_items=True)
        elif kind:
            cur["o"][kind] = _clean(chunk)

    for m in TOKEN_RE.finditer(t):
        num, let = m.group(1), m.group(2)
        if num is not None:
            n = int(num)
            if cur is None:
                ok = n == (first if first is not None else 1)
            else:
                ok = cur["n"] >= 2 and ((n == last + 1) if gap == 0 else (last < n <= last + 1 + gap))
            if ok:
                if cur is not None:
                    close(m.start())
                cur = {"q": len(qs) + 1, "raw": n, "t": "", "o": {}, "n": 0}
                qs.append(cur)
                last = n
                kind, start = "q", m.end()
            continue
        if cur is None:
            continue
        expect = chr(ord("a") + cur["n"])
        if let == expect.upper():  # faqat KATTA harf
            close(m.start())
            cur["n"] += 1
            kind, start = expect, m.end()
    if cur is not None:
        close(len(t))
    return qs


def _valid(qs) -> bool:
    return bool(qs) and all(len(q["o"]) >= 2 and q["t"] for q in qs)


def _first_number(t: str):
    for m in TOKEN_RE.finditer(t):
        if m.group(1) is not None:
            return int(m.group(1))
    return None


def _parse_joined(text: str):
    t = normalize_text(text)
    starts = [1]
    for m in TOKEN_RE.finditer(t):
        if m.group(1) is not None and int(m.group(1)) not in starts:
            starts.append(int(m.group(1)))
            if len(starts) >= 6:
                break
    best = None
    for first in starts:
        for gap in (0, 3):
            qs = _scan(t, first, gap)
            if _valid(qs) and (best is None or len(qs) > len(best)):
                best = qs
    if not best:
        return None
    for q in best:
        q.pop("n", None)
    return best


def _parse_parts(parts):
    """Har bir xabarni alohida tekshiradi: undagi birinchi raqam — o'sha savolning raqami."""
    allq = []
    for part in parts:
        t = normalize_text(part)
        first = _first_number(t)
        if first is None:
            return None
        qs = _scan(t, first, 0)
        if not qs:
            return None
        allq.extend(qs)
    if not _valid(allq):
        return None
    for i, q in enumerate(allq, 1):
        q["q"] = i
        q.pop("n", None)
    return allq


def parse_quiz(text: str, parts=None):
    """
    Savollarni matndan ajratadi. Savol — raqam (7. yoki 7)), variant — KATTA lotin harfi
    (A) yoki A.), kichik harf variant hisoblanmaydi. Qatorlarga bo'lingan ham, bir qatorda
    ketma-ket yozilgan ham ishlaydi. Raqamlash 1 dan boshlanmasa yoki ketma-ket bo'lmasa,
    savollar yuborilish tartibida 1 dan qayta raqamlanadi. Agar har bir savol alohida
    xabarda yuborilgan bo'lsa (parts), har xabardagi birinchi raqam shu savol raqami hisoblanadi.
    """
    best = _parse_joined(text)
    if parts and len(parts) > 1:
        alt = _parse_parts(parts)
        if alt and (best is None or len(alt) > len(best)):
            best = alt
    return best


def diagnose_quiz(text: str) -> str:
    """Savollar ajratilmaganda sababini tushuntiradi."""
    t = normalize_text(text)
    nums, lets = [], Counter()
    for m in TOKEN_RE.finditer(t):
        if m.group(1) is not None:
            nums.append(int(m.group(1)))
        else:
            lets[m.group(2).upper()] += 1
    out = [f"🔎 <b>Tahlil</b> (matn {len(text)} belgi):"]
    out.append(
        "• Savol raqamlari (<code>1.</code> yoki <code>1)</code>): "
        + (f"{len(nums)} ta, birinchilari: {', '.join(map(str, nums[:10]))}" if nums else "topilmadi ❌")
    )
    out.append(
        "• Variant belgilari (KATTA harf: <code>A)</code> yoki <code>A.</code>): "
        + (", ".join(f"{k}×{v}" for k, v in sorted(lets.items())) if lets else "topilmadi ❌")
    )
    if not lets and re.search(r"(?<![A-Za-z0-9'ʻʼ’`])[a-j]\s*[.),]", t):
        out.append("• Kichik harfli variantlar (a), b)...) topildi, lekin bot faqat <b>KATTA</b> harfni (A), B)...) taniydi ❗")
    odd = sorted({f"U+{ord(c):04X}" for c in text if unicodedata.category(c) in ("Cf", "Zs") and c != " "})
    if odd:
        out.append("• Ko'rinmas belgilar bor: " + ", ".join(odd[:6]) + " (bot ularni tozalaydi)")
    if nums and lets:
        qs = _scan(t, 1 if 1 in nums else nums[0], 0)
        bad = next((q for q in qs if len(q["o"]) < 2 or not q["t"]), None)
        if not qs:
            out.append("• Birinchi savol belgisi topilmadi.")
        elif bad:
            why = "savol matni bo'sh" if not bad["t"] else f"faqat {len(bad['o'])} ta variant topildi (kamida 2 kerak)"
            out.append(f"• <b>{bad['raw']}-savolda</b> {why}: «{html.escape((bad['t'] or '')[:70])}»")
    head = html.escape(t.strip()[:120].replace("\n", " ⏎ "))
    out.append(f"• Matn boshi: «{head}»")
    out.append(
        "\nTo'g'ri ko'rinish: <code>1. Savol matni</code> va keyin <code>A) variant</code>, "
        "<code>B) variant</code>... (KATTA lotin harflari, A dan boshlab ketma-ket)."
    )
    return "\n".join(out)


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
    raws = [q.get("raw", q["q"]) for q in qs]
    if any(r != q["q"] for r, q in zip(raws, qs)):
        if all(x < y for x, y in zip(raws, raws[1:])):
            note += f"\nℹ️ Savollar 1 dan qayta raqamlandi (asl raqamlar: {min(raws)}–{max(raws)})."
        else:
            note += "\nℹ️ Savollar yuborilish tartibi bo'yicha 1 dan qayta raqamlandi."
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
        "spent": int(min(max(time.time() - att["started"], 0), test["minutes"] * 60)),
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


def pub(res: dict) -> dict:
    """Yechuvchiga ko'rsatiladigan natija. Test egasi chiqargan odamga javoblar ko'rsatilmaydi."""
    if not res.get("kicked"):
        return res
    out = {k: v for k, v in res.items() if k not in ("wrong", "items")}
    out.update(wrong=[], items=[], hide_answers=True)
    return out


def fmt_spent(sec: int) -> str:
    m, sc = divmod(max(0, int(sec)), 60)
    return f"{m} daq {sc} s" if m else f"{sc} s"


def bar(pct: int, n: int = 10) -> str:
    k = max(0, min(n, round(pct / 100 * n)))
    return "▰" * k + "▱" * (n - k)


def _imul(a, b):
    return ((a & 0xFFFFFFFF) * (b & 0xFFFFFFFF)) & 0xFFFFFFFF


def _hash_str(st: str) -> int:
    h = (1779033703 ^ len(st)) & 0xFFFFFFFF
    for ch in st:
        h = _imul(h ^ ord(ch), 3432918353)
        h = ((h << 13) | (h >> 19)) & 0xFFFFFFFF
    return h


def _mulberry(a: int):
    state = [a & 0xFFFFFFFF]

    def rnd():
        state[0] = (state[0] + 0x6D2B79F5) & 0xFFFFFFFF
        a_ = state[0]
        t = _imul(a_ ^ (a_ >> 15), 1 | a_)
        t = ((t + _imul(t ^ (t >> 7), 61 | t)) & 0xFFFFFFFF) ^ t
        return ((t ^ (t >> 14)) & 0xFFFFFFFF) / 4294967296

    return rnd


def _shuf(arr, rnd):
    for i in range(len(arr) - 1, 0, -1):
        j = int(rnd() * (i + 1))
        arr[i], arr[j] = arr[j], arr[i]
    return arr


def view_order(test, uid):
    """Mini App'dagi aralashtirishning aynan nusxasi: (savollar tartibi, {savol: harflar tartibi})."""
    mode = test["shuffle"] or 0
    if test["kind"] != "quiz" or not mode or not test["questions"]:
        return None
    qd = {x["q"]: x for x in json.loads(test["questions"])}
    qs = sorted(decode_key(test["answer_key"]).keys())
    rnd = _mulberry(_hash_str(f"{test['code']}:{uid}"))
    seq = list(qs)
    _shuf(seq, rnd)
    perm = {}
    for q in qs:
        letters = list(qd[q]["o"].keys()) if q in qd else ["a", "b", "c", "d"]
        perm[q] = _shuf(letters[:], rnd) if mode >= 2 else letters
    return seq, perm


def result_text(r: dict, rank=None, test=None, uid=None) -> str:
    total = r["total"]
    pct = round(r["score"] / total * 100) if total else 0
    t = (
        f"📊 <b>{html.escape(r['title'])}</b>\n\n"
        f"{bar(pct)}  <b>{pct}%</b>\n\n"
        f"✅ To'g'ri javoblar: <b>{r['correct']}/{total}</b>\n"
        f"🚪 Jarima: -{r['penalties']}\n"
        f"🏆 Yakuniy ball: <b>{r['score']}</b>\n"
    )
    if r.get("spent") is not None:
        t += f"⏱ Sarflangan vaqt: {fmt_spent(r['spent'])}\n"
    if rank and rank[0]:
        t += f"📈 Hozirgi reyting: <b>{rank[0]}-o'rin</b> ({rank[1]} kishidan)\n"
    if r.get("kicked"):
        return t + "🚫 Test egasi tomonidan tugatildi\n🔒 Javoblar ko'rsatilmaydi"
    w = r["wrong"]
    if w:
        vo = view_order(test, uid) if test is not None else None
        if vo:
            seq, perm = vo

            def dl(q, l):
                if not l:
                    return "—"
                return chr(97 + perm[q].index(l)).upper() if q in perm and l in perm[q] else l.upper()

            rows = sorted((seq.index(x["q"]) + 1, dl(x["q"], x["given"]), dl(x["q"], x["right"])) for x in w)
            lines = [f"{n}) siz: {g} → to'g'ri: {rt}" for n, g, rt in rows[:60]]
        else:
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
                uid, prefix + result_text(res, rank_of(code, uid), get_test(code), uid),
                reply_markup=None if kicked else review_kb(code),
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
        return web.json_response({"finished": True, "result": pub(res), "kind": test["kind"], "qdata": None if res.get("kicked") else qdata_for(test), "shuffle": test["shuffle"] or 0, "seed": f"{code}:{uid}"})

    if camera_applies(test, uid) and not d.get("cam"):
        raise web.HTTPConflict(text="Kamera tekshiruvi o'tmagan. Ilovani yopib, qayta oching.")

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
        return web.json_response({"finished": True, "result": pub(res), "kind": test["kind"], "qdata": None if res.get("kicked") else qdata_for(test), "shuffle": test["shuffle"] or 0, "seed": f"{code}:{uid}"})
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
    if att["finished"] and att["result"] and json.loads(att["result"]).get("kicked"):
        raise web.HTTPForbidden(text="Ruxsat yo'q")  # chiqarilgan odamga test qayta ochilmaydi
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
        return web.json_response({"finished": True, "result": pub(res)})

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
        return web.json_response({"finished": True, "result": pub(res)})
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
    return web.json_response({"result": pub(res)})


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
        return web.json_response({"finished": True, "result": pub(res)})
    left = time_left(test, att)
    if left <= 0:
        res = await conclude(request.app["bot"], code, uid, "⌛ Vaqt tugadi.\n\n")
        return web.json_response({"finished": True, "result": pub(res)})
    return web.json_response({"finished": False, "left": left})


async def api_info(request):
    """Testni boshlamasdan oldin: kamera kerakmi? (urinish yaratilmaydi)"""
    d = await read_body(request)
    uid, _ = auth(d)
    code = str(d.get("code", "")).upper()
    test = get_test(code)
    if not test:
        raise web.HTTPNotFound(text="Test topilmadi")
    att = get_attempt(code, uid)
    return web.json_response(
        {
            "title": test["title"],
            "minutes": test["minutes"],
            "camera": camera_applies(test, uid),
            "camera_secs": test["camera_secs"] or 7,
            "pilot": (test["camera"] or 0) == 2,
            "finished": bool(att and att["finished"]),
            "block": None if att else start_block(test, uid),
        }
    )


FACE_LAST = {}


async def api_face(request):
    """Yuz ko'rinmaganda: -1 ball. Video yuborilmaydi, faqat signal."""
    d = await read_body(request)
    uid, _ = auth(d)
    code = str(d.get("code", "")).upper()
    test, att = get_test(code), get_attempt(code, uid)
    if not test or not att or att["finished"] or not camera_applies(test, uid):
        raise web.HTTPConflict(text="expired")
    key, now = (code, uid), time.time()
    if now - FACE_LAST.get(key, 0) < 5:  # takroriy signalni e'tiborsiz qoldiradi
        return web.json_response({"penalties": att["penalties"] * PENALTY})
    FACE_LAST[key] = now
    db.execute(
        "UPDATE attempts SET penalties=penalties+1, face_n=face_n+1 WHERE code=? AND user_id=?",
        (code, uid),
    )
    db.commit()
    touch(code, uid)
    att = get_attempt(code, uid)
    return web.json_response({"penalties": att["penalties"] * PENALTY})


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
            web.post("/api/info", api_info),
            web.post("/api/face", api_face),
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
.rhero{background:linear-gradient(135deg,#161a4d,#2d33a0);color:#fff;border-radius:24px;padding:20px 16px 18px;text-align:center;box-shadow:0 10px 26px rgba(22,26,77,.35);animation:qin .4s ease}
.rtitle{font-weight:700;font-size:18px;margin-bottom:4px;word-break:break-word}
.rkick{background:rgba(229,57,53,.25);border:1px solid #e53935;border-radius:12px;padding:6px 10px;font-weight:600;font-size:13px;margin:8px 0}
.rhero .donut{margin:10px auto 8px}
.rhero .donut b{animation:pop .7s cubic-bezier(.2,1.4,.4,1) both}
.rverdict{font-weight:700;font-size:18px}
.rsub{opacity:.8;font-size:14px;margin-top:4px}
.rtiles{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;margin:14px 0}
.rtiles.three{grid-template-columns:repeat(3,1fr)}
.camwrap{width:min(250px,70%);aspect-ratio:3/4;margin:14px auto;border-radius:22px;overflow:hidden;border:3px solid #4db35a;background:#000;box-shadow:0 8px 24px var(--qshadow)}
.camwrap video,.camprev video{width:100%;height:100%;object-fit:cover;transform:scaleX(-1)}
.camprev{position:fixed;right:12px;bottom:12px;width:84px;height:112px;border-radius:16px;overflow:hidden;border:3px solid #4db35a;background:#000;z-index:25;box-shadow:0 6px 18px rgba(0,0,0,.35)}
.camprev.bad{border-color:#e53935;animation:pulse 1s infinite}
.camprev b{position:absolute;left:0;right:0;bottom:0;background:rgba(229,57,53,.9);color:#fff;font-size:12px;text-align:center;padding:2px 0}
body.cam .qwrap{padding-bottom:150px}
.tile{background:var(--qcard);border-radius:16px;padding:12px 4px;text-align:center;box-shadow:0 6px 16px var(--qshadow);animation:pop .5s ease both}
.tile:nth-child(2){animation-delay:.08s}
.tile:nth-child(3){animation-delay:.16s}
.tile:nth-child(4){animation-delay:.24s}
.tile span{display:block;font-size:18px}
.tile b{display:block;font-size:22px;margin-top:2px}
.tile i{display:block;font-style:normal;font-size:11px;color:var(--qmuted);margin-top:2px}
@keyframes pop{from{opacity:0;transform:translateY(10px) scale(.92)}to{opacity:1;transform:none}}
.rpen{background:var(--badbg);border-radius:14px;padding:10px 12px;text-align:center;margin-bottom:14px;font-size:14px}
.rsec{background:var(--qcard);border-radius:20px;padding:14px 14px 6px;box-shadow:0 6px 16px var(--qshadow);margin-bottom:16px}
.rh{font-weight:700;margin-bottom:6px}
.erow{display:flex;align-items:center;gap:10px;padding:9px 0}
.erow + .erow{border-top:1px solid var(--qline)}
.en{flex:none;width:30px;height:30px;border-radius:50%;background:var(--badbg);color:#e53935;font-weight:700;font-size:13px;display:flex;align-items:center;justify-content:center}
.ech{display:flex;align-items:center;flex-wrap:wrap;gap:6px}
.chip{padding:4px 10px;border-radius:999px;font-size:13px;font-weight:600}
.chip.bad{background:var(--badbg);color:#e53935}
.chip.good{background:var(--goodbg);color:#3aa655}
.chip.none{background:var(--qsoft);color:var(--qmuted)}
.arr{color:var(--qmuted)}
.big.grad{background:linear-gradient(135deg,var(--pri),#7b86ff);color:#fff;box-shadow:0 8px 18px rgba(91,103,232,.35);margin-bottom:10px}
.big.ghost{background:var(--qcard);color:var(--qtx);border:1px solid var(--qline)}
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

<div id="s-res" class="hidden qwrap">
  <div class="rhero">
    <div class="rtitle" id="r-title"></div>
    <div id="r-kick" class="hidden rkick">🚫 Test egasi tomonidan tugatildi</div>
    <div class="donut" id="r-donut"></div>
    <div class="rverdict" id="r-verdict"></div>
    <div class="rsub" id="r-sub"></div>
  </div>
  <div class="rtiles" id="r-tiles">
    <div class="tile"><span>✅</span><b id="r-ok">0</b><i>To'g'ri</i></div>
    <div class="tile"><span>❌</span><b id="r-bad">0</b><i>Xato</i></div>
    <div class="tile" id="t-none"><span>⬜</span><b id="r-none">0</b><i>Javobsiz</i></div>
    <div class="tile"><span>🏆</span><b id="r-score">0</b><i>Ball</i></div>
  </div>
  <div class="rpen hidden" id="r-penbox">🚪 Jarima (ilovadan chiqish, kamera): <b id="r-pen"></b></div>
  <div class="rsec hidden" id="r-wrongbox"><div class="rh">❌ Xatolar</div><div id="r-wrong"></div></div>
  <button class="big grad" id="revbtn">🔍 Xatolarni tahlil qilish</button>
  <button class="big ghost" id="closebtn">Yopish</button>
</div>

<div id="s-cam" class="hidden qwrap">
  <div class="rhero">
    <div class="rtitle" id="c-title"></div>
    <div style="font-size:42px;margin:6px 0">📷</div>
    <div class="rverdict">Kamera kerak</div>
    <div class="rsub" id="c-text" style="line-height:1.5"></div>
  </div>
  <div class="camwrap hidden" id="c-vwrap"><video id="c-video" playsinline muted autoplay></video></div>
  <div class="qwarn" id="c-status" style="text-align:center;margin:12px 0"></div>
  <button class="big grad" id="c-btn">📷 Kamerani yoqish</button>
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

<div id="camprev" class="camprev hidden"><video id="m-video" playsinline muted autoplay></video><b id="m-badge" class="hidden"></b></div>

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
  ["load", "test", "quiz", "cam", "res", "rev"].forEach(n => $("s-" + n).classList.toggle("hidden", n !== name));
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
function fatal(msg) { $("s-load").textContent = "❌ " + msg; show("load"); }
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
function ensureOrder() {
  if (isQuiz() && !SEQ.length) { QD = {}; S.qdata.forEach(x => { QD[x.q] = x; }); prepOrder(); }
}
function fmtSpent(sec) {
  sec = Math.max(0, Math.round(sec));
  const m = Math.floor(sec / 60), s = sec % 60;
  return (m ? m + " daq " : "") + s + " s";
}
function chipEl(cls, txt) {
  const c = document.createElement("span"); c.className = "chip " + cls; c.textContent = txt;
  return c;
}
function showResult(r) {
  finished = true;
  stopCam();
  RES = r;
  try { tg.disableClosingConfirmation(); } catch (e) {}
  ensureOrder();
  $("r-title").textContent = r.title;
  $("r-kick").classList.toggle("hidden", !r.kicked);
  const total = r.total, pct = total ? Math.round(r.score / total * 100) : 0;
  const col = pct >= 80 ? "#2fb344" : (pct >= 50 ? "#f5a623" : "#e53935");
  const C = 2 * Math.PI * 54;
  $("r-donut").innerHTML = '<svg width="140" height="140" viewBox="0 0 140 140">' +
    '<circle cx="70" cy="70" r="54" fill="none" stroke="rgba(255,255,255,.18)" stroke-width="14"/>' +
    '<circle cx="70" cy="70" r="54" fill="none" stroke="' + col + '" stroke-width="14" stroke-linecap="round" ' +
    'stroke-dasharray="' + C.toFixed(1) + '" stroke-dashoffset="' + C.toFixed(1) + '"/></svg>' +
    '<b style="color:#fff">' + pct + '%</b>';
  setTimeout(() => {
    const arc = $("r-donut").querySelectorAll("circle")[1];
    if (arc) { arc.style.transition = "stroke-dashoffset 1s ease"; arc.style.strokeDashoffset = (C * (1 - pct / 100)).toFixed(1); }
  }, 60);
  const wrong = r.wrong || [];
  const none = wrong.filter(x => !x.given).length;
  const hide = !!(r.kicked || r.hide_answers);   // chiqarilgan odamga javoblar ko'rsatilmaydi
  $("t-none").classList.toggle("hidden", hide);
  $("r-tiles").classList.toggle("three", hide);
  $("revbtn").classList.toggle("hidden", hide);
  $("r-ok").textContent = r.correct;
  $("r-bad").textContent = hide ? Math.max(0, total - r.correct) : wrong.length - none;
  $("r-none").textContent = none;
  $("r-score").textContent = r.score;
  $("r-verdict").textContent = pct === 100 ? "Mukammal! 🏆" : pct >= 80 ? "Ajoyib natija! 🎉" : pct >= 60 ? "Yaxshi natija 👍" :
    pct >= 40 ? "Yomon emas, takrorlash foyda beradi 📚" : "Mavzuni qayta o'qib chiqing 💪";
  $("r-sub").textContent = r.correct + "/" + total + " to'g'ri javob" + (r.spent != null ? "  ·  ⏱ " + fmtSpent(r.spent) : "");
  $("r-penbox").classList.toggle("hidden", !(r.penalties > 0));
  $("r-pen").textContent = "-" + r.penalties;
  const w = $("r-wrong"); w.innerHTML = "";
  $("r-wrongbox").classList.toggle("hidden", hide || wrong.length === 0);
  const disp = (q, l) => {
    if (!l) return "—";
    const i = (isQuiz() && PERM[q]) ? PERM[q].indexOf(l) : -1;
    return (i >= 0 ? String.fromCharCode(97 + i) : l).toUpperCase();
  };
  const pos = q => { const i = isQuiz() ? SEQ.indexOf(q) : -1; return i >= 0 ? i + 1 : q; };
  wrong.map(x => ({n: pos(x.q), g: disp(x.q, x.given), t: disp(x.q, x.right), none: !x.given}))
    .sort((a, b) => a.n - b.n)
    .forEach(e => {
      const row = document.createElement("div"); row.className = "erow";
      const n = document.createElement("span"); n.className = "en"; n.textContent = e.n;
      const ch = document.createElement("div"); ch.className = "ech";
      ch.appendChild(e.none ? chipEl("none", "Javobsiz") : chipEl("bad", "Sizniki: " + e.g));
      const ar = document.createElement("span"); ar.className = "arr"; ar.textContent = "→";
      ch.appendChild(ar);
      ch.appendChild(chipEl("good", "To'g'ri: " + e.t));
      row.appendChild(n); row.appendChild(ch);
      w.appendChild(row);
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
    ensureOrder();
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
  CAM.lastSeen = Date.now();   // ilovadan qaytgach yuz hisobi qaytadan boshlanadi
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

/* ---- Kamera: yuz ko'rinib turishini telefonning o'zi tekshiradi (video yuborilmaydi) ---- */
const MP_VER = "0.10.14";
const MP_BASE = "https://cdn.jsdelivr.net/npm/@mediapipe/tasks-vision@" + MP_VER;
const MP_MODEL = "https://storage.googleapis.com/mediapipe-models/face_detector/blaze_face_short_range/float16/1/blaze_face_short_range.tflite";
let CAM = {stream: null, detector: null, secs: 7, lastSeen: 0, absent: false, busy: false, timer: 0, on: false};
async function loadDetector() {
  if (window.__camTest) return window.__camTest;   // faqat sinov uchun
  try {
    const mp = await import(MP_BASE + "/vision_bundle.mjs");
    const files = await mp.FilesetResolver.forVisionTasks(MP_BASE + "/wasm");
    const make = delegate => mp.FaceDetector.createFromOptions(files, {
      baseOptions: {modelAssetPath: MP_MODEL, delegate: delegate}, runningMode: "VIDEO", minDetectionConfidence: 0.5
    });
    let det;
    try { det = await make("GPU"); } catch (e) { det = await make("CPU"); }
    return {count: async v => det.detectForVideo(v, performance.now()).detections.length};
  } catch (e) {
    if (window.FaceDetector) {
      const fd = new window.FaceDetector({fastMode: true, maxDetectedFaces: 2});
      return {count: async v => (await fd.detect(v)).length};
    }
    throw e;
  }
}
function camError(e) {
  const n = e && e.name;
  if (n === "NotAllowedError" || n === "SecurityError") return "Kameraga ruxsat berilmadi. Telefon sozlamalarida Telegram uchun kameraga ruxsat bering va qayta urining.";
  if (n === "NotFoundError" || n === "OverconstrainedError") return "Kamera topilmadi.";
  if (n === "NotReadableError") return "Kamera band. Uni ishlatayotgan boshqa ilovani yoping va qayta urining.";
  return "Kamera yoki yuz aniqlash modeli yuklanmadi (internetni tekshiring). " + ((e && e.message) || "");
}
function setCamStatus(t) { $("c-status").textContent = t; }
function camSetup(info) {
  return new Promise(resolve => {
    CAM.secs = info.camera_secs || 7;
    $("c-title").textContent = info.title;
    $("c-text").textContent = "Bu testda yechuvchi kadrda ko'rinib turishi kerak. Kamera tasviri telefoningizdan chiqmaydi, yozib olinmaydi va test egasiga ko'rsatilmaydi: yuzni telefonning o'zi tekshiradi. " +
      CAM.secs + " soniya ketma-ket yuz ko'rinmasa, -1 ball ayriladi." + (info.pilot ? " (Sinov rejimi: kamera faqat test egasi uchun yoqilgan.)" : "");
    show("cam");
    const btn = $("c-btn");
    btn.onclick = async () => {
      btn.disabled = true;
      try {
        setCamStatus("📷 Kamera yoqilmoqda...");
        CAM.stream = await navigator.mediaDevices.getUserMedia({video: {facingMode: "user"}, audio: false});
        const v = $("c-video"); v.srcObject = CAM.stream; $("c-vwrap").classList.remove("hidden");
        try { await v.play(); } catch (e) {}
        setCamStatus("⏳ Yuz aniqlash modeli yuklanmoqda (bir necha soniya)...");
        CAM.detector = await loadDetector();
      } catch (e) {
        setCamStatus("❌ " + camError(e));
        btn.disabled = false; btn.textContent = "🔄 Qayta urinish";
        return;
      }
      setCamStatus("🙂 Yuzingizni kadrga qo'ying...");
      let ok = 0, tries = 0;
      const tid = setInterval(async () => {
        if (CAM.busy) return;
        CAM.busy = true;
        let n = 0;
        try { n = await CAM.detector.count($("c-video")); } catch (e) {}
        CAM.busy = false;
        ok = n > 0 ? ok + 1 : 0; tries++;
        if (ok >= 3) { clearInterval(tid); setCamStatus("✅ Yuz aniqlandi"); resolve(); }
        else if (tries === 40) setCamStatus("Yuz aniqlanmayapti. Yorug'roq joyda, telefonni yuz oldida tuting.");
      }, 500);
    };
  });
}
function startCamLoop() {
  CAM.on = true; CAM.lastSeen = Date.now(); CAM.absent = false;
  document.body.classList.add("cam");
  $("m-video").srcObject = CAM.stream;
  try { $("m-video").play(); } catch (e) {}
  $("camprev").classList.remove("hidden");
  CAM.timer = setInterval(camTick, 500);
}
async function camTick() {
  if (!CAM.on || finished || away || CAM.busy) return;
  CAM.busy = true;
  let n = 1;
  try {
    const tr = CAM.stream && CAM.stream.getVideoTracks()[0];
    n = (tr && tr.readyState === "live") ? await CAM.detector.count($("m-video")) : 0;
  } catch (e) { n = 1; }   // aniqlagich xato bersa, noto'g'ri jarima bermaymiz
  CAM.busy = false;
  const now = Date.now();
  if (n > 0) { CAM.lastSeen = now; CAM.absent = false; }
  const gap = (now - CAM.lastSeen) / 1000;
  $("camprev").classList.toggle("bad", gap > 2);
  $("m-badge").classList.toggle("hidden", !(gap > 2));
  $("m-badge").textContent = "⏱ " + Math.max(0, Math.ceil(CAM.secs - gap)) + " s";
  if (gap >= CAM.secs && !CAM.absent) { CAM.absent = true; reportAbsent(); }
}
async function reportAbsent() {
  haptic("warning"); toast("📷 Yuz ko'rinmadi: -1 ball");
  try { const r = await api("/api/face"); setPen(r.penalties); } catch (e) {}
}
function stopCam() {
  CAM.on = false;
  if (CAM.timer) { clearInterval(CAM.timer); CAM.timer = 0; }
  try { if (CAM.stream) CAM.stream.getTracks().forEach(t => t.stop()); } catch (e) {}
  CAM.stream = null;
  document.body.classList.remove("cam");
  $("camprev").classList.add("hidden");
}

/* ---- Boshlash ---- */
(async function init() {
  if (!INIT || !CODE) { fatal("Bu sahifani Telegram bot orqali oching."); return; }
  let info = {camera: false};
  try { info = await api("/api/info"); } catch (e) { fatal(e.message); return; }
  if (info.block) { fatal(info.block); return; }
  if (info.camera && !info.finished) await camSetup(info);
  try { S = await api("/api/start", {cam: !!info.camera}); } catch (e) { stopCam(); fatal(e.message); return; }
  if (S.finished) { stopCam(); showResult(S.result); return; }
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
  if (info.camera) startCamLoop();
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
        "Matnni shu ko'rinishda yozsangiz, har bir savol variantlari bilan alohida sahifada chiqadi "
        "(variant harflari faqat <b>KATTA</b> bo'lsin; har bir savolni alohida xabar qilib yuborsangiz ham bo'ladi, "
        "xabardagi birinchi raqam shu savolning raqami):\n"
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
        extra = ("\n\n" + diagnose_quiz(text)) if text else ""
        await m.answer(
            "ℹ️ Word fayldan savollarni ajratib bo'lmadi (raqam va harflar avtomatik ro'yxat bo'lishi mumkin). "
            "Fayl o'z holicha ko'rsatiladi." + extra
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
    qs = parse_quiz(body, parts)
    if qs:
        await state.update_data(
            kind="quiz", body=body, file_id="", questions=json.dumps(qs, ensure_ascii=False)
        )
        await c.message.answer(quiz_note(qs) + "\nHar biri alohida sahifada ko'rsatiladi.")
    else:
        await state.update_data(kind="text", body=body, file_id="", questions=None)
        await c.message.answer(
            "ℹ️ Savol va variantlar aniqlanmadi, matn oddiy ko'rinishda ko'rsatiladi.\n\n" + diagnose_quiz(body)
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
            "Siz bu testni allaqachon yechib bo'lgansiz.\n\n" + result_text(res, None, test, uid),
            reply_markup=None if res.get("kicked") else review_kb(code),
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
        cam = f" | 📷 {r['face_n']}×" if r["face_n"] else ""
        lines.append(
            f"• <b>{html.escape(name)}</b> — {st}\n"
            f"   ⏱ {fmt_left(time_left(test, r))} | ✍️ {done}/{total}{pen}{cam}"
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
    "📄 /nusxa KOD — testdan yangi kodli nusxa\n"
    "📷 /kamera KOD on|off|sinov [soniya] — yechuvchi kadrda ko'rinishini tekshirish"
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
    w.writerow(["№", "Ism", "To'g'ri", "Jami", "Foiz", "Jarima", "Ball", "Holat", "Boshlagan", "Tugatgan", "Sarflangan (daq)", "Kamera (marta)"])
    for i, a in enumerate(rows, 1):
        res = json.loads(a["result"]) if a["result"] else {}
        if a["finished"]:
            holat = "chiqarilgan" if res.get("kicked") else "tugatgan"
            pct = round(a["score"] / a["total"] * 100) if a["total"] else 0
            spent = round((a["finished_at"] - a["started"]) / 60, 1) if a["finished_at"] else ""
            row = [a["correct"], a["total"], pct, a["penalties"] * PENALTY, a["score"], holat,
                   fmt_dt(a["started"]), fmt_dt(a["finished_at"]) if a["finished_at"] else "", spent, a["face_n"] or 0]
        else:
            row = ["", "", "", a["penalties"] * PENALTY, "", "yechmoqda", fmt_dt(a["started"]), "", "", a["face_n"] or 0]
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
        "INSERT INTO tests(code,owner_id,title,file_id,kind,answer_key,minutes,created,body,questions,shuffle,camera,camera_secs) "
        "VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)",
        (new, test["owner_id"], (test["title"] + " (nusxa)")[:100], test["file_id"], test["kind"],
         test["answer_key"], test["minutes"], time.time(), test["body"], test["questions"], test["shuffle"] or 0,
         test["camera"] or 0, test["camera_secs"] or 7),
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


CAMERA_MODES = {"off": 0, "on": 1, "sinov": 2}


def camera_status(test) -> str:
    mode, secs = test["camera"] or 0, test["camera_secs"] or 7
    if mode == 0:
        return "📷 Kamera tekshiruvi: o'chiq"
    who = "hamma yechuvchi uchun" if mode == 1 else "faqat siz (test egasi) yechganingizda — sinov rejimi"
    return f"📷 Kamera tekshiruvi: yoqiq ({who}). {secs} soniya ketma-ket yuz ko'rinmasa, -1 ball."


@router.message(Command("kamera"))
async def camera_cmd(m: Message, command: CommandObject):
    r = await own_test(m, command, "/kamera KOD on|off|sinov [soniya]")
    if not r:
        return
    code, test, rest = r
    if not rest:
        return await m.answer(
            camera_status(test) + "\n\nO'zgartirish: <code>/kamera KOD on|off|sinov [soniya]</code>\n"
            "• <b>sinov</b> — faqat siz uchun (boshqalarga kamera so'ralmaydi)\n"
            "• <b>on</b> — hamma yechuvchi uchun\n• <b>off</b> — o'chiq"
        )
    mode = CAMERA_MODES.get(rest[0].lower())
    if mode is None:
        return await m.answer("Ishlatish: <code>/kamera KOD on|off|sinov [soniya]</code>")
    secs = test["camera_secs"] or 7
    if len(rest) > 1:
        if not rest[1].isdigit() or not 3 <= int(rest[1]) <= 120:
            return await m.answer("Soniya 3 dan 120 gacha bo'lsin. Masalan: <code>/kamera KOD sinov 20</code>")
        secs = int(rest[1])
    db.execute("UPDATE tests SET camera=?, camera_secs=? WHERE code=?", (mode, secs, code))
    db.commit()
    await m.answer(
        camera_status(get_test(code))
        + "\n\nYechuvchiga test oldidan ogohlantirish chiqadi: video telefondan chiqmaydi, saqlanmaydi va "
        "sizga ko'rsatilmaydi, faqat \"yuz ko'rinmadi\" signali yuboriladi."
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
