"""Log the userbot in from the terminal and save the session to MongoDB (same place /userbot uses).

    python3 login_userbot.py

Needs the .env of the bot (API_ID, API_HASH, MONGO_URI). Type the phone number, the code Telegram sends
and (if the account has it) the 2FA password right here, nothing goes through Telegram chats.
"""
import asyncio

from motor.motor_asyncio import AsyncIOMotorClient
from pyrogram import Client

import config


async def main():
    if not config.MONGO_URI:
        raise SystemExit("MONGO_URI is empty in .env")
    async with Client("login_tmp", api_id=config.API_ID, api_hash=config.API_HASH, in_memory=True) as app:
        me = await app.get_me()
        session = await app.export_session_string()
    db = AsyncIOMotorClient(config.MONGO_URI)[config.MONGO_DB]
    await db["settings"].update_one({"_id": "userbot"},
                                    {"$set": {"session": session, "name": me.first_name or "", "id": me.id}}, upsert=True)
    print(f"Done: userbot {me.first_name} (id {me.id}) saved. Restart the bot.")


asyncio.run(main())