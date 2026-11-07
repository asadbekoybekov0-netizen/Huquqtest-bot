"""
Telegram TEST BOT (aiogram 3.x)

O'rnatish:   pip install aiogram
Ishga tushirish:
    export BOT_TOKEN="123456:ABC..."      (Windows: set BOT_TOKEN=...)
    python bot.py
"""
import asyncio
import logging
import os
import random
import re
import sqlite3
import string
import time

from aiogram import Bot, Dispatcher, F, Router
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
)

BOT_TOKEN = os.getenv("BOT_TOKEN", "")
PENALTY = 1  # chiqib ketganda ayriladigan ball

ALLOWED_MIME = {
    "application/pdf",
    "application/msword",
    "application/vnd.openxmlformats-officedocument.wordprocessingml.document",
}

# ----------------------------- BAZA -----------------------------
db = sqlite3.connect("tests.db", check_same_thread=False)
db.row_factory = sqlite3.Row
db.executescript(
    """
CREATE TABLE IF NOT EXISTS tests(
    code TEXT PRIMARY KEY, owner_id INTEGER, title TEXT,
    file_id TEXT, answer_key TEXT, minutes INTEGER, created REAL);
CREATE TABLE IF NOT EXISTS attempts(
    code TEXT, user_id INTEGER, name TEXT, started REAL,
    finished INTEGER DEFAULT 0, correct INTEGER DEFAULT 0, total INTEGER DEFAULT 0,
    penalties INTEGER DEFAULT 0, score INTEGER DEFAULT 0,
    PRIMARY KEY(code, user_id));
"""
)


def get_test(code):
    return db.execute("SELECT * FROM tests WHERE code=?", (code,)).fetchone()


def get_attempt(code, uid):
    return db.execute(
        "SELECT * FROM attempts WHERE code=? AND user_id=?", (code, uid)
    ).fetchone()


# ----------------------------- YORDAMCHI -----------------------------
def parse_answers(text: str) -> dict:
    """'abcd' yoki '1a 2b 3c' yoki '1-a,2-b' ko'rinishini {raqam: harf} ga aylantiradi."""
    text = text.strip().lower()
    pairs = re.findall(r"(\d+)\s*[-.:)]*\s*([a-z])", text)
    if pairs:
        return {int(n): l for n, l in pairs}
    return {i + 1: l for i, l in enumerate(re.findall(r"[a-z]", text))}


def encode_key(d: dict) -> str:
    return ",".join(f"{n}{l}" for n, l in sorted(d.items()))


def decode_key(s: str) -> dict:
    return {int(p[:-1]): p[-1] for p in s.split(",") if p}


def new_code() -> str:
    while True:
        c = "".join(random.choices(string.ascii_uppercase + string.digits, k=6))
        if not get_test(c):
            return c


def fmt_time(sec: float) -> str:
    sec = max(0, int(sec))
    return f"{sec // 60:02d}:{sec % 60:02d}"


def finalize(code: str, uid: int, given: dict | None) -> str:
    """Natijani hisoblaydi, bazaga yozadi va matn qaytaradi."""
    test, att = get_test(code), get_attempt(code, uid)
    key = decode_key(test["answer_key"])
    given = given or {}
    correct = sum(1 for n, l in key.items() if given.get(n) == l)
    total = len(key)
    score = max(0, correct - att["penalties"] * PENALTY)
    db.execute(
        "UPDATE attempts SET finished=1, correct=?, total=?, score=? WHERE code=? AND user_id=?",
        (correct, total, score, code, uid),
    )
    db.commit()

    wrong = [
        f"{n}) siz: {given.get(n, '—').upper()} → to'g'ri: {l.upper()}"
        for n, l in sorted(key.items())
        if given.get(n) != l
    ]
    text = (
        f"📊 <b>{test['title']}</b> natijasi\n\n"
        f"✅ To'g'ri: {correct}/{total}\n"
        f"🚪 Chiqib ketish jarimasi: -{att['penalties'] * PENALTY}\n"
        f"🏆 Yakuniy ball: <b>{score}</b>\n"
    )
    if wrong:
        text += "\n❌ <b>Xatolar:</b>\n" + "\n".join(wrong[:60])
        if len(wrong) > 60:
            text += f"\n... va yana {len(wrong) - 60} ta"
    else:
        text += "\n🎉 Xatosiz!"
    return text


def exit_kb(code: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="🚪 Testdan chiqish (-1)", callback_data=f"exit:{code}")]]
    )


menu_kb = ReplyKeyboardMarkup(
    keyboard=[
        [KeyboardButton(text="➕ Test yaratish"), KeyboardButton(text="✍️ Testni yechish")],
        [KeyboardButton(text="📊 Mening testlarim")],
    ],
    resize_keyboard=True,
)


# ----------------------------- HOLATLAR -----------------------------
class Create(StatesGroup):
    title = State()
    file = State()
    key = State()
    minutes = State()


class Join(StatesGroup):
    code = State()


class Solve(StatesGroup):
    answering = State()


router = Router()


# ----------------------------- TAYMER -----------------------------
async def timer_task(bot: Bot, code: str, uid: int, delay: float):
    if delay > 120:
        await asyncio.sleep(delay - 60)
        att = get_attempt(code, uid)
        if att and not att["finished"]:
            await bot.send_message(uid, "⏰ Vaqtning tugashiga 1 daqiqa qoldi!")
        await asyncio.sleep(60)
    else:
        await asyncio.sleep(max(delay, 0))
    att = get_attempt(code, uid)
    if att and not att["finished"]:
        text = finalize(code, uid, {})
        await bot.send_message(uid, "⌛ Vaqt tugadi, javob yuborilmadi.\n\n" + text)
        await notify_owner(bot, code, uid)


async def notify_owner(bot: Bot, code: str, uid: int):
    test, att = get_test(code), get_attempt(code, uid)
    try:
        await bot.send_message(
            test["owner_id"],
            f"🔔 <b>{test['title']}</b> ({code})\n"
            f"{att['name']} tugatdi: {att['correct']}/{att['total']}, "
            f"jarima: -{att['penalties']}, ball: <b>{att['score']}</b>",
        )
    except Exception:
        pass


# ----------------------------- START / MENYU -----------------------------
@router.message(CommandStart())
async def cmd_start(m: Message, state: FSMContext, command: CommandObject, bot: Bot):
    # Test yechish paytida /start bosilsa — chiqib ketgan deb hisoblanadi
    if await state.get_state() == Solve.answering.state:
        data = await state.get_data()
        att = get_attempt(data.get("code"), m.from_user.id)
        if att and not att["finished"]:
            db.execute(
                "UPDATE attempts SET penalties=penalties+1 WHERE code=? AND user_id=?",
                (data["code"], m.from_user.id),
            )
            db.commit()
            await m.answer("⚠️ Testni tark etdingiz: -1 ball. Vaqt ketmoqda!")
    await state.clear()

    if command.args:  # t.me/bot?start=KOD
        return await begin_attempt(m, state, bot, command.args.strip().upper())
    await m.answer(
        "👋 Salom! Bu test boti.\n\n"
        "➕ Test yarating va kodni ulashing\n"
        "✍️ Yoki kod bilan testni yeching",
        reply_markup=menu_kb,
    )


# ----------------------------- TEST YARATISH -----------------------------
@router.message(F.text == "➕ Test yaratish", StateFilter(None))
async def create_start(m: Message, state: FSMContext):
    await state.set_state(Create.title)
    await m.answer("Test nomini yuboring:")


@router.message(Create.title, F.text)
async def create_title(m: Message, state: FSMContext):
    await state.update_data(title=m.text.strip()[:100])
    await state.set_state(Create.file)
    await m.answer("Test faylini yuboring (PDF yoki Word):")


@router.message(Create.file, F.document)
async def create_file_step(m: Message, state: FSMContext):
    if m.document.mime_type not in ALLOWED_MIME:
        return await m.answer("❌ Faqat PDF yoki Word (.doc/.docx) fayl yuboring.")
    await state.update_data(file_id=m.document.file_id)
    await state.set_state(Create.key)
    await m.answer(
        "Javoblar kalitini yuboring.\n\n"
        "Misol: <code>abcdabcdab</code>\n"
        "yoki: <code>1a 2b 3c 4d</code>"
    )


@router.message(Create.file)
async def create_file_wrong(m: Message):
    await m.answer("Iltimos, fayl (PDF yoki Word) yuboring.")


@router.message(Create.key, F.text)
async def create_key(m: Message, state: FSMContext):
    key = parse_answers(m.text)
    if not key:
        return await m.answer("❌ Javoblar topilmadi. Qayta yuboring (masalan: abcdabcd).")
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
        "INSERT INTO tests VALUES(?,?,?,?,?,?,?)",
        (code, m.from_user.id, data["title"], data["file_id"], data["key"], int(m.text), time.time()),
    )
    db.commit()
    await state.clear()
    me = await bot.get_me()
    await m.answer(
        f"🎉 Test tayyor!\n\n"
        f"📌 Nomi: {data['title']}\n"
        f"🔑 Kod: <code>{code}</code>\n"
        f"⏱ Vaqt: {m.text} daqiqa\n\n"
        f"Havola: https://t.me/{me.username}?start={code}\n"
        f"Natijalar: /natijalar {code}",
        reply_markup=menu_kb,
    )


# ----------------------------- TESTNI BOSHLASH -----------------------------
@router.message(F.text == "✍️ Testni yechish", StateFilter(None))
async def join_start(m: Message, state: FSMContext):
    await state.set_state(Join.code)
    await m.answer("Test kodini kiriting:")


@router.message(Join.code, F.text)
async def join_code(m: Message, state: FSMContext, bot: Bot):
    await begin_attempt(m, state, bot, m.text.strip().upper())


async def begin_attempt(m: Message, state: FSMContext, bot: Bot, code: str):
    test = get_test(code)
    if not test:
        await state.clear()
        return await m.answer("❌ Bunday kodli test topilmadi.", reply_markup=menu_kb)

    uid = m.from_user.id
    att = get_attempt(code, uid)
    if att and att["finished"]:
        await state.clear()
        return await m.answer("Siz bu testni allaqachon yechib bo'lgansiz.", reply_markup=menu_kb)

    new = att is None
    if new:
        db.execute(
            "INSERT INTO attempts(code,user_id,name,started) VALUES(?,?,?,?)",
            (code, uid, m.from_user.full_name, time.time()),
        )
        db.commit()
        att = get_attempt(code, uid)

    left = att["started"] + test["minutes"] * 60 - time.time()
    if left <= 0:
        await state.clear()
        text = finalize(code, uid, {})
        await notify_owner(bot, code, uid)
        return await m.answer("⌛ Vaqt tugagan.\n\n" + text, reply_markup=menu_kb)

    total = len(decode_key(test["answer_key"]))
    await state.set_state(Solve.answering)
    await state.update_data(code=code)
    await m.answer_document(
        test["file_id"],
        caption=(
            f"📝 <b>{test['title']}</b>\n"
            f"Savollar: {total} ta\n"
            f"⏱ Qolgan vaqt: {fmt_time(left)}\n\n"
            f"Javoblarni <b>bitta xabarda</b> yuboring:\n"
            f"<code>abcdabcd...</code> yoki <code>1a 2b 3c</code>\n\n"
            f"⚠️ Testdan chiqsangiz -1 ball."
        ),
        reply_markup=exit_kb(code),
    )
    if new:
        asyncio.create_task(timer_task(bot, code, uid, left))


# ----------------------------- YECHISH -----------------------------
@router.message(Solve.answering, F.text)
async def submit(m: Message, state: FSMContext, bot: Bot):
    data = await state.get_data()
    code, uid = data["code"], m.from_user.id
    att = get_attempt(code, uid)
    if not att or att["finished"]:
        await state.clear()
        return await m.answer("Test yakunlangan.", reply_markup=menu_kb)

    test = get_test(code)
    if time.time() > att["started"] + test["minutes"] * 60:
        text = finalize(code, uid, {})
        await state.clear()
        await notify_owner(bot, code, uid)
        return await m.answer("⌛ Vaqt tugadi.\n\n" + text, reply_markup=menu_kb)

    given = parse_answers(m.text)
    if not given:
        return await m.answer("Javoblar topilmadi. Masalan: abcdabcd")

    text = finalize(code, uid, given)
    await state.clear()
    await m.answer(text, reply_markup=menu_kb)
    await notify_owner(bot, code, uid)


@router.callback_query(F.data.startswith("exit:"))
async def exit_test(c: CallbackQuery, state: FSMContext):
    code, uid = c.data.split(":")[1], c.from_user.id
    att = get_attempt(code, uid)
    if not att or att["finished"]:
        return await c.answer("Test yakunlangan.", show_alert=True)
    db.execute(
        "UPDATE attempts SET penalties=penalties+1 WHERE code=? AND user_id=?", (code, uid)
    )
    db.commit()
    await state.clear()
    await c.message.answer(
        "🚪 Testdan chiqdingiz: <b>-1 ball</b>.\n"
        "Vaqt ketmoqda! Qaytish uchun kodni qayta kiriting.",
        reply_markup=menu_kb,
    )
    await c.answer("-1 ball")


# ----------------------------- NATIJALAR (test egasi uchun) -----------------------------
@router.message(F.text == "📊 Mening testlarim", StateFilter(None))
async def my_tests(m: Message):
    rows = db.execute("SELECT * FROM tests WHERE owner_id=?", (m.from_user.id,)).fetchall()
    if not rows:
        return await m.answer("Sizda hali test yo'q.")
    lines = [f"• {r['title']} — <code>{r['code']}</code>  (/natijalar {r['code']})" for r in rows]
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
        st = f"{r['correct']}/{r['total']}, jarima -{r['penalties']}, ball {r['score']}" if r["finished"] else "yechmoqda..."
        lines.append(f"{i}. {r['name']} — {st}")
    await m.answer(f"📊 <b>{test['title']}</b>\n\n" + "\n".join(lines))


# ----------------------------- ISHGA TUSHIRISH -----------------------------
async def main():
    if not BOT_TOKEN:
        raise SystemExit("BOT_TOKEN o'rnatilmagan!")
    logging.basicConfig(level=logging.INFO)
    from aiogram.client.default import DefaultBotProperties
    from aiogram.enums import ParseMode

    bot = Bot(BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(router)
    await dp.start_polling(bot)


if __name__ == "__main__":
    asyncio.run(main())
