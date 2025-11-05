import os
import json
import random
import logging
from datetime import datetime, timezone
from typing import Optional, Tuple, List, Dict
import xml.etree.ElementTree as ET
import re

import discord
from discord.ext import tasks
from dotenv import load_dotenv
import requests
from discord import Embed, Colour
from discord.ui import View, Button
from server import keep_alive
# =========================
# Setup & configuration
# =========================
keep_alive()
load_dotenv()
log = logging.getLogger("yt-discord-bot")
DISCORD_TOKEN = os.getenv("DISCORD_TOKEN")
GUILD_ID = int(os.getenv("GUILD_ID", "0"))

# YouTube stats (Data API used ONLY for these)
YOUTUBE_API_KEY = os.getenv("YOUTUBE_API_KEY")
YOUTUBE_CHANNEL_ID = os.getenv("YOUTUBE_CHANNEL_ID")  # canonical UC... ID

# Category for grouping the voice channels
VOICE_CATEGORY_NAME = os.getenv("VOICE_CATEGORY_NAME", "YouTube Stats").strip()

# Goal to display
SUBS_GOAL = int(os.getenv("SUBS_GOAL", "1000"))
LIVE_ALERT_CHANNEL_ID = int(os.getenv("LIVE_ALERT_CHANNEL_ID", "0"))
log.info("Configured LIVE_ALERT_CHANNEL_ID: %s", LIVE_ALERT_CHANNEL_ID)

# Schedules (minutes)
STATS_INTERVAL_MIN = int(os.getenv("STATS_INTERVAL_MIN", "720"))        # 12 hours
RSS_REFRESH_MIN = int(os.getenv("RSS_REFRESH_MIN", "60"))                # hourly
REMINDER_INTERVAL_MIN = int(os.getenv("REMINDER_INTERVAL_MIN", "1"))     # one post per minute

# Channel for “old video” reminders (Text Channel ID)
REMINDER_CHANNEL_ID = int(os.getenv("REMINDER_CHANNEL_ID", "0"))

# Local persistence for RSS accumulation
RSS_CACHE_PATH = os.getenv("RSS_CACHE_PATH", "rss_cache.json")

# Persisted channel IDs to avoid duplicates across reconnects
CHANNEL_ID_STORE = os.getenv("CHANNEL_ID_STORE", "channel_ids.json")

logging.basicConfig(level=logging.INFO)
log = logging.getLogger("yt-discord-bot")

# =========================
# Discord client
# =========================
intents = discord.Intents.default()
intents.guilds = True
intents.members = True
bot = discord.Client(intents=intents)

# Voice channel IDs (set/created at runtime)
VC_SUBS_ID: Optional[int] = None
VC_VIEWS_ID: Optional[int] = None
VC_VIDEOS_ID: Optional[int] = None
VC_GOAL_ID: Optional[int] = None
VC_MEMBERS_ID: Optional[int] = None
VC_LIVE_ID: Optional[int] = None

# Caches
_last_stats: Optional[Tuple[int, int, int]] = None
_last_members: Optional[int] = None
_last_live_state: Optional[bool] = None

# In-memory reminder queue
reminder_queue: List[Dict] = []

# Channel branding cache (filled during stats loop)
_channel_meta = {
    "title": None,
    "avatar_url": None,
    "banner_url": None,
    "channel_url": None,
}

# One-time guard for on_ready
_ready_once = False

# =========================
# Persistence for channel IDs
# =========================
def load_ids() -> Dict[str, int]:
    if os.path.exists(CHANNEL_ID_STORE):
        try:
            with open(CHANNEL_ID_STORE, "r", encoding="utf-8") as f:
                data = json.load(f)
            return {k: int(v) for k, v in data.items() if isinstance(v, (int, str)) and str(v).isdigit()}
        except Exception as e:
            log.exception("Failed to load channel ID store: %s", e)
    return {}

def save_ids(ids: Dict[str, Optional[int]]) -> None:
    try:
        serializable = {k: int(v) for k, v in ids.items() if v}
        with open(CHANNEL_ID_STORE, "w", encoding="utf-8") as f:
            json.dump(serializable, f, indent=2)
    except Exception as e:
        log.exception("Failed to save channel ID store: %s", e)

_id_cache = load_ids()
VC_SUBS_ID = _id_cache.get("subs")
VC_VIEWS_ID = _id_cache.get("views")
VC_VIDEOS_ID = _id_cache.get("videos")
VC_GOAL_ID = _id_cache.get("goal")
VC_MEMBERS_ID = _id_cache.get("members")
VC_LIVE_ID = _id_cache.get("live")

# =========================
# Helpers
# =========================
def youtube_watch_url(video_id: str) -> str:
    return f"https://www.youtube.com/watch?v={video_id}"

def default_thumb(video_id: str) -> str:
    return f"https://i.ytimg.com/vi/{video_id}/hqdefault.jpg"

def fmt_num(n: int) -> str:
    return f"{n:,}"

# =========================
# Voice channels bootstrap
# =========================
READ_ONLY_DEFAULTS = {
    "subs":   "📊 Subs: 0",
    "views":  "👁️ Views: 0",
    "videos": "🎞️ Videos: 0",
    "goal":   "🎯 Goal: 0",
    "members":"👥 Members: 0",
    "live":   "🔴 OFFLINE",
}

async def deny_connect_permissions(vc: discord.VoiceChannel, guild: discord.Guild):
    """Make the voice channel visible but not joinable (read-only display)."""
    everyone = guild.default_role
    overwrites = vc.overwrites_for(everyone)
    changed = False
    if overwrites.view_channel is not True:
        overwrites.view_channel = True
        changed = True
    if overwrites.connect is not False:
        overwrites.connect = False
        changed = True
    if changed:
        try:
            await vc.set_permissions(everyone, overwrite=overwrites, reason="Read-only stats channel")
        except discord.Forbidden:
            log.error("Missing permission to set overwrites on %s", vc.name)
        except discord.HTTPException as e:
            log.error("HTTP error setting overwrites on %s: %s", vc.name, e)

async def ensure_stats_voice_channels(guild: discord.Guild):
    """Create/find Subs, Views, Videos, Goal, Members, and Live read-only voice channels under a category."""
    global VC_SUBS_ID, VC_VIEWS_ID, VC_VIDEOS_ID, VC_GOAL_ID, VC_MEMBERS_ID, VC_LIVE_ID, _id_cache

    # Resolve or create category
    category = None
    if VOICE_CATEGORY_NAME:
        category = discord.utils.get(guild.categories, name=VOICE_CATEGORY_NAME)
        if category is None:
            try:
                category = await guild.create_category(VOICE_CATEGORY_NAME, reason="Create YouTube stats category")
                log.info("Created category: %s", VOICE_CATEGORY_NAME)
            except discord.Forbidden:
                log.warning("Missing permission to create category: %s", VOICE_CATEGORY_NAME)
            except discord.HTTPException as e:
                log.error("HTTP error creating category: %s", e)

    # Helper: prefer existing channel by ID
    def by_id(i: Optional[int]) -> Optional[discord.VoiceChannel]:
        if not i:
            return None
        ch = guild.get_channel(int(i))
        return ch if isinstance(ch, discord.VoiceChannel) else None

    # Helper: exact name in category, else prefix fallback
    def find_vc_by_name_or_prefix(default_name: str) -> Optional[discord.VoiceChannel]:
        # FIX: make prefix a string, not a list
        prefix = default_name.split(":", 1)[0] if ":" in default_name else default_name
        # Exact match first
        for ch in guild.voice_channels:
            same_category = (category is None) or (ch.category_id == (category.id if category else None))
            if same_category and ch.name == default_name:
                return ch
        # Prefix fallback
        for ch in guild.voice_channels:
            same_category = (category is None) or (ch.category_id == (category.id if category else None))
            if same_category and isinstance(ch.name, str) and ch.name.startswith(prefix):
                return ch
        return None  # [2][1]

    targets = [
        ("subs",   READ_ONLY_DEFAULTS["subs"]),
        ("views",  READ_ONLY_DEFAULTS["views"]),
        ("videos", READ_ONLY_DEFAULTS["videos"]),
        ("goal",   READ_ONLY_DEFAULTS["goal"]),
        ("members",READ_ONLY_DEFAULTS["members"]),
        ("live",   READ_ONLY_DEFAULTS["live"]),
    ]

    resolved: Dict[str, discord.VoiceChannel] = {}

    # First try by IDs to avoid duplicates
    id_map = {
        "subs": VC_SUBS_ID,
        "views": VC_VIEWS_ID,
        "videos": VC_VIDEOS_ID,
        "goal": VC_GOAL_ID,
        "members": VC_MEMBERS_ID,
        "live": VC_LIVE_ID,
    }
    for key, _default_name in targets:
        ch = by_id(id_map.get(key))
        if ch:
            await deny_connect_permissions(ch, guild)
            resolved[key] = ch

    # Then discover or create missing ones
    for key, default_name in targets:
        if key in resolved:
            continue
        existing = None
        if key == "live":
            for live_prefix in ("🟢 LIVE", "🔴 OFFLINE"):
                existing = find_vc_by_name_or_prefix(live_prefix)
                if existing:
                    break
            if not existing:
                existing = find_vc_by_name_or_prefix(default_name)
        else:
            existing = find_vc_by_name_or_prefix(default_name)

        if existing is None:
            try:
                vc = await guild.create_voice_channel(
                    name=default_name,
                    category=category,
                    reason=f"Create {key} stats voice channel"
                )
                await deny_connect_permissions(vc, guild)
                resolved[key] = vc
                log.info("Created voice channel: %s (%s)", vc.name, vc.id)
            except discord.Forbidden:
                log.error("Missing Manage Channels permission to create %s channel.", key)
                continue
            except discord.HTTPException as e:
                log.error("Discord HTTP error creating %s channel: %s", key, e)
                continue
        else:
            await deny_connect_permissions(existing, guild)
            resolved[key] = existing

    # Store IDs and persist
    VC_SUBS_ID    = resolved.get("subs").id    if resolved.get("subs")    else VC_SUBS_ID
    VC_VIEWS_ID   = resolved.get("views").id   if resolved.get("views")   else VC_VIEWS_ID
    VC_VIDEOS_ID  = resolved.get("videos").id  if resolved.get("videos")  else VC_VIDEOS_ID
    VC_GOAL_ID    = resolved.get("goal").id    if resolved.get("goal")    else VC_GOAL_ID
    VC_MEMBERS_ID = resolved.get("members").id if resolved.get("members") else VC_MEMBERS_ID
    VC_LIVE_ID    = resolved.get("live").id    if resolved.get("live")    else VC_LIVE_ID

    _id_cache.update({
        "subs": VC_SUBS_ID, "views": VC_VIEWS_ID, "videos": VC_VIDEOS_ID,
        "goal": VC_GOAL_ID, "members": VC_MEMBERS_ID, "live": VC_LIVE_ID
    })
    save_ids(_id_cache)

# =========================
# YouTube stats + branding (API usage)
# =========================
def yt_channels_statistics(api_key: str, channel_id: str) -> Optional[Tuple[int, int, int]]:
    """Return (subs, views, videos) from channels.list statistics."""
    try:
        url = (
            "https://www.googleapis.com/youtube/v3/channels"
            f"?part=statistics&id={channel_id}&key={api_key}"
        )
        r = requests.get(url, timeout=15)
        r.raise_for_status()
        data = r.json()
        items = data.get("items", [])
        if not isinstance(items, list) or not items:
            log.error("YouTube channels.list returned no items for id=%s (verify UC… ID).", channel_id)
            return None
        stats = items[0].get("statistics", {}) or {}
        subs = int(stats.get("subscriberCount", 0))
        views = int(stats.get("viewCount", 0))
        videos = int(stats.get("videoCount", 0))
        return subs, views, videos
    except requests.HTTPError as e:
        try:
            log.error("YouTube HTTPError: %s | %s", e, e.response.json())
        except Exception:
            log.error("YouTube HTTPError: %s", e)
    except Exception as e:
        log.exception("Error fetching channel statistics: %s", e)
    return None  # items per schema [4]

def yt_channel_metadata(api_key: str, channel_id: str) -> Optional[dict]:
    """Fetch channel branding once per stats cycle: title, avatar, banner, channel URL."""
    try:
        url = (
            "https://www.googleapis.com/youtube/v3/channels"
            f"?part=snippet,brandingSettings&id={channel_id}&key={api_key}"
        )
        r = requests.get(url, timeout=15)
        r.raise_for_status()
        data = r.json()
        items = data.get("items", [])
        if not isinstance(items, list) or not items:
            log.error("No channel metadata for id=%s", channel_id)
            return None
        it = items[0]
        snippet = it.get("snippet", {}) or {}
        branding = it.get("brandingSettings", {}) or {}
        title = snippet.get("title") or "YouTube Channel"
        thumbs = snippet.get("thumbnails") or {}
        avatar = (thumbs.get("high") or thumbs.get("medium") or thumbs.get("default") or {}).get("url")
        image = branding.get("image") or {}
        banner_base = image.get("bannerExternalUrl")
        banner = f"{banner_base}=w2480" if banner_base else None
        channel_url = f"https://www.youtube.com/channel/{channel_id}"
        return {
            "title": title,
            "avatar_url": avatar,
            "banner_url": banner,
            "channel_url": channel_url,
        }
    except requests.HTTPError as e:
        try:
            log.error("YouTube HTTPError (metadata): %s | %s", e, e.response.json())
        except Exception:
            log.error("YouTube HTTPError (metadata): %s", e)
    except Exception as e:
        log.exception("Error fetching channel metadata: %s", e)
    return None  # items per schema [4]

async def update_stats_channels(guild: discord.Guild, stats: Tuple[int, int, int]):
    """Update Subs, Views, Videos, Goal channels."""
    global _last_stats
    if stats == _last_stats:
        return
    _last_stats = stats
    subs, views, videos = stats
    updates = [
        (VC_SUBS_ID,   f"📊 Subs: {fmt_num(subs)}"),
        (VC_VIEWS_ID,  f"👁️ Views: {fmt_num(views)}"),
        (VC_VIDEOS_ID, f"🎞️ Videos: {fmt_num(videos)}"),
        (VC_GOAL_ID,   f"🎯 Goal: {fmt_num(SUBS_GOAL)}"),
    ]
    for ch_id, name in updates:
        if not ch_id:
            continue
        ch = guild.get_channel(ch_id)
        if not isinstance(ch, discord.VoiceChannel):
            continue
        try:
            await ch.edit(name=name, reason="Update YouTube statistics")
            await deny_connect_permissions(ch, guild)
        except discord.Forbidden:
            log.error("Missing permission to edit %s", ch.name)
        except discord.HTTPException as e:
            log.error("Discord HTTP error updating %s: %s", ch.name, e)

# =========================
# Members channel updates
# =========================
async def refresh_members_channel(guild: discord.Guild):
    """Update Members voice channel immediately."""
    global _last_members
    count = guild.member_count  # includes bots
    if VC_MEMBERS_ID is None:
        return
    if _last_members == count:
        return
    _last_members = count
    ch = guild.get_channel(VC_MEMBERS_ID)
    if isinstance(ch, discord.VoiceChannel):
        try:
            await ch.edit(name=f"👥 Members: {count:,}", reason="Member count change")
            await deny_connect_permissions(ch, guild)
        except discord.Forbidden:
            log.error("Missing permission to edit Members channel.")
        except discord.HTTPException as e:
            log.error("Discord HTTP error updating Members channel: %s", e)

@bot.event
async def on_member_join(member: discord.Member):
    if member.guild.id == GUILD_ID:
        await refresh_members_channel(member.guild)

@bot.event
async def on_member_remove(member: discord.Member):
    if member.guild.id == GUILD_ID:
        await refresh_members_channel(member.guild)

# =========================
# RSS: collect uploads (no Data API)
# =========================
def channel_rss_url(channel_id: str) -> str:
    return f"https://www.youtube.com/feeds/videos.xml?channel_id={channel_id}"

def parse_rss_entries(xml_text: str) -> List[Dict]:
    """Parse Atom feed entries into [{id,title,link,thumb}]"""
    ns = {
        "atom": "http://www.w3.org/2005/Atom",
        "media": "http://search.yahoo.com/mrss/",
        "yt": "http://www.youtube.com/xml/schemas/2015",
    }
    root = ET.fromstring(xml_text)
    out: List[Dict] = []
    for entry in root.findall("atom:entry", ns):
        title_el = entry.find("atom:title", ns)
        link_el = entry.find("atom:link", ns)
        video_id_el = entry.find("yt:videoId", ns)
        media_group = entry.find("media:group", ns)
        title = title_el.text if title_el is not None else "Video"
        link = link_el.attrib.get("href") if link_el is not None else None
        video_id = video_id_el.text if video_id_el is not None else None
        thumb_url = None
        if media_group is not None:
            thumbs = media_group.findall("media:thumbnail", ns)
            if thumbs:
                thumb_url = thumbs[-1].attrib.get("url")
        if video_id and link:
            out.append({"id": video_id, "title": title, "link": link, "thumb": thumb_url})
    return out

def load_rss_cache(path: str) -> Dict[str, Dict]:
    try:
        if os.path.exists(path):
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            return {k: v for k, v in data.items() if isinstance(k, str) and isinstance(v, dict)}
    except Exception as e:
        log.exception("Failed to load RSS cache: %s", e)
    return {}

def save_rss_cache(path: str, cache: Dict[str, Dict]) -> None:
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(cache, f, ensure_ascii=False, indent=2)
    except Exception as e:
        log.exception("Failed to save RSS cache: %s", e)

def accumulate_from_rss(cache: Dict[str, Dict], entries: List[Dict]) -> int:
    added = 0
    for e in entries:
        vid = e["id"]
        if vid not in cache:
            cache[vid] = e
            added += 1
        else:
            cache[vid].update({k: v for k, v in e.items() if v})
    return added

# =========================
# Reminder posting (no Data API)
# =========================
REMINDER_CAPTIONS = [
    "From the vault—give this a watch!",
    "Throwback upload you might have missed!",
    "ICYMI: a classic from the channel!",
    "Reminder: this video is worth revisiting!",
    "Rewatch time! Check this out!",
]

def build_embed_for_entry(entry: Dict) -> Embed:
    """Build a branded embed."""
    title = entry.get("title") or "Video"
    vid = entry["id"]
    url = entry.get("link") or youtube_watch_url(vid)
    thumb = entry.get("thumb") or default_thumb(vid)
    e = Embed(
        title=title,
        description=random.choice(REMINDER_CAPTIONS),
        colour=Colour.purple(),
        timestamp=datetime.now(timezone.utc),
    )
    e.url = url
    ch_title = _channel_meta.get("title") or "YouTube Channel"
    ch_url = _channel_meta.get("channel_url") or f"https://www.youtube.com/channel/{YOUTUBE_CHANNEL_ID}"
    ch_avatar = _channel_meta.get("avatar_url")
    if ch_avatar:
        e.set_author(name=ch_title, url=ch_url, icon_url=ch_avatar)
    else:
        e.set_author(name=ch_title, url=ch_url)
    banner = _channel_meta.get("banner_url")
    if banner:
        e.set_image(url=banner)
    e.set_thumbnail(url=thumb)
    return e

class WatchView(View):
    def __init__(self, url: str):
        super().__init__(timeout=None)
        self.add_item(Button(label="Watch", style=discord.ButtonStyle.link, url=url))

# =========================
# Background tasks
# =========================
@tasks.loop(minutes=RSS_REFRESH_MIN)
async def rss_refresh_loop():
    """Fetch the channel's RSS feed (no Data API) and accumulate entries; rebuild the in-memory queue."""
    await bot.wait_until_ready()
    if not YOUTUBE_CHANNEL_ID:
        return
    url = channel_rss_url(YOUTUBE_CHANNEL_ID)
    try:
        r = requests.get(url, timeout=15)
        r.raise_for_status()
        entries = parse_rss_entries(r.text)
    except requests.HTTPError as e:
        log.error("RSS HTTP error: %s", e)
        return
    except Exception as e:
        log.exception("Error parsing RSS: %s", e)
        return
    cache = load_rss_cache(RSS_CACHE_PATH)
    added = accumulate_from_rss(cache, entries)
    if added:
        save_rss_cache(RSS_CACHE_PATH, cache)
    global reminder_queue
    reminder_queue = list(cache.values())
    random.shuffle(reminder_queue)
    if added:
        log.info("RSS refresh added %d new entries; queue size now %d", added, len(reminder_queue))

@tasks.loop(minutes=REMINDER_INTERVAL_MIN)
async def reminder_loop():
    """Post exactly one old-video reminder per interval using the accumulated RSS cache."""
    await bot.wait_until_ready()
    if REMINDER_CHANNEL_ID == 0:
        return
    guild = bot.get_guild(GUILD_ID)
    if guild is None:
        return
    channel = guild.get_channel(REMINDER_CHANNEL_ID)
    if not isinstance(channel, discord.TextChannel):
        return
    global reminder_queue
    if not reminder_queue:
        cache = load_rss_cache(RSS_CACHE_PATH)
        reminder_queue = list(cache.values())
        random.shuffle(reminder_queue)
        if not reminder_queue:
            log.info("Reminder queue empty; no post this minute.")
            return
    entry = reminder_queue.pop()
    vid = entry["id"]
    url = entry.get("link") or youtube_watch_url(vid)
    try:
        await channel.send(embed=build_embed_for_entry(entry), view=WatchView(url))
        log.info("Posted reminder: %s", entry.get("title"))
    except discord.Forbidden:
        log.error("Missing permission to send in reminder channel.")
    except discord.HTTPException as e:
        log.error("Discord HTTP error sending reminder: %s", e)
    insert_at = random.randint(0, max(0, len(reminder_queue)))
    reminder_queue.insert(insert_at, entry)

@tasks.loop(minutes=STATS_INTERVAL_MIN)
async def stats_loop():
    """Fetch channel-wide stats via Data API (subs, views, videos) and update display channels; refresh branding."""
    await bot.wait_until_ready()
    guild = bot.get_guild(GUILD_ID)
    if guild is None:
        return
    # Only ensure channels if any ID is missing to avoid duplicate creation
    if any(x is None for x in (VC_SUBS_ID, VC_VIEWS_ID, VC_VIDEOS_ID, VC_GOAL_ID, VC_MEMBERS_ID, VC_LIVE_ID)):
        await ensure_stats_voice_channels(guild)
    if not (YOUTUBE_API_KEY and YOUTUBE_CHANNEL_ID):
        log.warning("YOUTUBE_API_KEY or YOUTUBE_CHANNEL_ID missing; skipping stats update.")
        return
    stats = yt_channels_statistics(YOUTUBE_API_KEY, YOUTUBE_CHANNEL_ID)
    if stats is not None:
        await update_stats_channels(guild, stats)
        await refresh_members_channel(guild)
    meta = yt_channel_metadata(YOUTUBE_API_KEY, YOUTUBE_CHANNEL_ID)
    if meta:
        _channel_meta.update(meta)

# =========================
# Live status (no API)
# =========================
# =========================
# Live status (with UPCOMING + notifications)
# =========================
# =========================
# Live status (with UPCOMING + notifications)
# =========================
YTLIVE_URL = "https://www.youtube.com/channel/{channel_id}/live"
CANONICAL_RE = re.compile(
    r'<link[^>]+rel=["\']canonical["\'][^>]+href=["\']([^"\']+)["\']',
    re.IGNORECASE
)

def yt_is_live_noapi(channel_id: str, timeout: int = 12) -> Optional[str]:
    """
    Return one of:
      "live"     → channel currently live
      "upcoming" → stream scheduled but not live yet
      "offline"  → no live/upcoming
      None       → inconclusive (network/parse error)
    Also dumps the HTML to debug_live.html if inconclusive.
    """
    url = YTLIVE_URL.format(channel_id=channel_id)
    headers = {"User-Agent": "Mozilla/5.0", "Accept-Language": "en"}
    cookies = {"CONSENT": "YES+cb.20210420-15-p1.en-GB+FX+634"}

    try:
        r = requests.get(url, headers=headers, cookies=cookies, timeout=timeout)
        r.raise_for_status()
        html = r.text

        # 1. Canonical link
        m = CANONICAL_RE.search(html)
        if m:
            href = m.group(1)

            # If canonical is a watch URL → assume live (fallback) + double-check
            if "/watch" in href:
                try:
                    r2 = requests.get(href, headers=headers, cookies=cookies, timeout=timeout)
                    r2.raise_for_status()
                    html2 = r2.text
                    if '"isLiveBroadcast":true' in html2 or '"status":"LIVE"' in html2:
                        return "live"
                    if '"isUpcoming":true' in html2 or '"upcomingEventData"' in html2:
                        return "upcoming"
                    if '"isLiveBroadcast":false' in html2 or '"status":"OFFLINE"' in html2:
                        return "offline"
                except Exception as e:
                    log.warning("Failed to follow canonical watch URL: %s", e)
                return "live"  # fallback: canonical pointed to watch

            if "/channel/" in href:
                return "offline"

        # 2. JSON flags in initial /live page
        if '"isLiveBroadcast":true' in html or '"status":"LIVE"' in html:
            return "live"
        if '"isLiveBroadcast":false' in html or '"status":"OFFLINE"' in html:
            return "offline"

        # 3. Scheduled streams
        if '"isUpcoming":true' in html or '"upcomingEventData"' in html:
            return "upcoming"

        # If nothing matched → dump HTML for debugging
        with open("debug_live.html", "w", encoding="utf-8") as f:
            f.write(html)
        log.info("Dumped inconclusive HTML to debug_live.html")

        return None

    except requests.RequestException as e:
        log.error("Live check failed: %s", e)
        return None

@tasks.loop(seconds=90)
async def live_status_loop_noapi():
    """Poll /live page without API and rename the Live voice channel on changes + send notifications."""
    await bot.wait_until_ready()
    if not YOUTUBE_CHANNEL_ID:
        return
    guild = bot.get_guild(GUILD_ID)
    if guild is None or VC_LIVE_ID is None:
        return
    ch = guild.get_channel(VC_LIVE_ID)
    if not isinstance(ch, discord.VoiceChannel):
        return

    state = yt_is_live_noapi(YOUTUBE_CHANNEL_ID)
    if state is None:
        log.info("Live status check inconclusive; keeping previous state.")
        return

    global _last_live_state
    if _last_live_state == state:
        return
    _last_live_state = state

    # Pick channel name + notification info
    if state == "live":
        target_name = "🟢 LIVE"
        notification_title = "🔴 The channel is now LIVE!"
        colour = Colour.red()
    elif state == "upcoming":
        target_name = "🟡 UPCOMING"
        notification_title = "🟡 A stream is scheduled!"
        colour = Colour.gold()
    else:
        target_name = "🔴 OFFLINE"
        notification_title = "⚫ The channel went offline."
        colour = Colour.dark_grey()

    # Update VC channel
    if ch.name != target_name:
        try:
            await ch.edit(name=target_name, reason="Update live status (no API)")
            await deny_connect_permissions(ch, guild)
            log.info("Updated live channel to: %s", target_name)
        except discord.Forbidden:
            log.error("Missing permission to edit Live channel.")
        except discord.HTTPException as e:
            log.error("Discord HTTP error updating Live channel: %s", e)

    # Send notification if configured
    if LIVE_ALERT_CHANNEL_ID != 0:
        notif_channel = guild.get_channel(LIVE_ALERT_CHANNEL_ID)
        if isinstance(notif_channel, discord.TextChannel):
            embed = Embed(
                title=notification_title,
                description=f"[Click here to visit the channel]({_channel_meta.get('channel_url') or f'https://www.youtube.com/channel/{YOUTUBE_CHANNEL_ID}'})",
                colour=colour,
                timestamp=datetime.now(timezone.utc),
            )

            # Add channel branding
            if _channel_meta.get("avatar_url"):
                embed.set_author(
                    name=_channel_meta.get("title") or "YouTube Channel",
                    url=_channel_meta.get("channel_url") or f"https://www.youtube.com/channel/{YOUTUBE_CHANNEL_ID}",
                    icon_url=_channel_meta["avatar_url"],
                )
            else:
                embed.set_author(
                    name=_channel_meta.get("title") or "YouTube Channel",
                    url=_channel_meta.get("channel_url") or f"https://www.youtube.com/channel/{YOUTUBE_CHANNEL_ID}",
                )

            try:
                # 👇 One clean send with @everyone + embed
                await notif_channel.send(content="@everyone", embed=embed, delete_after=60)
                log.info("Sent live state notification: %s", notification_title)
            except discord.Forbidden:
                log.error("Missing permission to send in live alert channel.")
            except discord.HTTPException as e:
                log.error("Discord HTTP error sending live notification: %s", e)







# =========================
# Ready & entrypoint
# =========================
@bot.event
async def on_ready():
    global _ready_once
    if _ready_once:
        log.info("on_ready called again; skipping one-time setup.")
        return  # prevent duplicate setup on reconnects
    _ready_once = True

    log.info("Logged in as %s (ID: %s)", bot.user, bot.user.id)
    await bot.change_presence(
        activity=discord.Activity(
            type=discord.ActivityType.watching,
            name="SneakyDevilz Gaming Channel"
        ),
        status=discord.Status.online
    )

    guild = bot.get_guild(GUILD_ID)
    if guild:
        await ensure_stats_voice_channels(guild)
        await refresh_members_channel(guild)

    # Initial RSS load
    try:
        if YOUTUBE_CHANNEL_ID:
            url = channel_rss_url(YOUTUBE_CHANNEL_ID)
            r = requests.get(url, timeout=15)
            r.raise_for_status()
            entries = parse_rss_entries(r.text)
            cache = load_rss_cache(RSS_CACHE_PATH)
            added = accumulate_from_rss(cache, entries)
            if added:
                save_rss_cache(RSS_CACHE_PATH, cache)
            global reminder_queue
            reminder_queue = list(cache.values())
            random.shuffle(reminder_queue)
            log.info("Initial RSS load: %d items in queue", len(reminder_queue))
    except Exception as e:
        log.exception("Initial RSS load failed: %s", e)

    # Start loops (idempotent)
    if not stats_loop.is_running():
        stats_loop.start()
    if not rss_refresh_loop.is_running():
        rss_refresh_loop.start()
    if not reminder_loop.is_running():
        reminder_loop.start()
    if not live_status_loop_noapi.is_running():
        live_status_loop_noapi.start()

if __name__ == "__main__":
    required = [
        ("DISCORD_TOKEN", DISCORD_TOKEN),
        ("GUILD_ID", GUILD_ID),
        ("YOUTUBE_API_KEY", YOUTUBE_API_KEY),
        ("YOUTUBE_CHANNEL_ID", YOUTUBE_CHANNEL_ID),
    ]
    missing = [k for k, v in required if not v or (k == "GUILD_ID" and int(v) == 0)]
    if missing:
        raise SystemExit(f"Missing env vars: {', '.join(missing)}")
    bot.run(DISCORD_TOKEN)

