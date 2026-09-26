import base64
import hashlib
from cryptography.fernet import Fernet, InvalidToken
import hmac
import secrets
import uuid
from decimal import Decimal, InvalidOperation, ROUND_HALF_UP
from email.parser import BytesParser
from email.policy import default as EMAIL_POLICY
from http.cookies import SimpleCookie
import io
import json
import mimetypes
import os
import random
import re
import socket
import sqlite3
import datetime
import ipaddress
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from PIL import Image

MOVIE_FOLDER = "MOVIES_DC1"
PORT = int(os.environ.get("PORT", "9284"))
BASE_DIR = Path(__file__).resolve().parent
DATABASE_FILE = str(BASE_DIR / "notflix.db")
DATABASE_LOCK = threading.RLock()
MAX_JSON_BODY_BYTES = 1 * 1024 * 1024
AUTH_RATE_LIMIT = 8
AUTH_RATE_WINDOW_SECONDS = 5 * 60
WRITE_RATE_LIMIT = 120
WRITE_RATE_WINDOW_SECONDS = 60
LOGO_EXTENSIONS = [".png", ".jpg", ".jpeg", ".webp"]
VIDEO_EXTENSIONS = [".mp4"]
LINK_EXTENSIONS = [".url", ".link", ".youtube", ".yt"]
TEXT_LINK_PREFIXES = ("youtube_", "yt_")
CHUNK_SIZE = 128 * 2048
ACCOUNT_FOLDER = "ACCOUNTS"
AUTH_FOLDER = "AUTH"
USERS_FILE_NAME = "users.json"
PROFILE_PICTURE_FOLDER = "PROFILE_PICTURES"
CHAT_FOLDER = "CHAT"
GLOBAL_CHAT_FILE_NAME = "global.json"
DIRECT_CHAT_FOLDER = "DIRECT"
SESSION_COOKIE_NAME = "notflix_session"
SESSION_TTL_SECONDS = 7 * 24 * 60 * 60
USERNAME_PATTERN = re.compile(r"^[A-Za-z0-9_]{3,20}$")
PROFILE_PICTURE_EXTENSIONS = {".png", ".jpg", ".jpeg", ".webp", ".gif"}
MAX_PROFILE_PICTURE_BYTES = 2 * 1024 * 1024
MAX_CHAT_MESSAGE_LENGTH = 10000
MAX_GLOBAL_CHAT_MESSAGES = 50000
MAX_DIRECT_CHAT_MESSAGES = 50000
AUTH_LOCK = threading.RLock()
CHAT_LOCK = threading.RLock()
SESSIONS = {}
RATE_LIMITS = {}
RATE_LIMIT_LOCK = threading.Lock()
WATCHED_FILE_NAME = "watched.json"
CONTINUE_FILE_NAME = "continue.json"
PLAYLISTS_FILE_NAME = "playlists.json"
MINECRAFT_PROFILE_FILE_NAME = "minecraft.json"
SOCIALS_FILE_NAME = "socials.json"
SOCIALS_KEY_FILE_NAME = "socials.key"
DRAWINGS_FOLDER = "DRAWINGS"
DRAWINGS_CATALOG_FILE = "drawings.json"
FEEDBACK_FOLDER = "FEEDBACK"
FEEDBACK_FILE_NAME = "feedback.json"
MAX_DRAWING_BYTES = 900 * 1024
MAX_DRAWING_TITLE = 100
MAX_FEEDBACK_LENGTH = 4000
ADMIN_FEEDBACK_USERNAME = "Raphuz"
RAPHUZ_BOOTSTRAP_PASSWORD = os.environ.get("NOTFLIX_RAPHUZ_PASSWORD", "RTXgamer180!")
SOCIAL_OAUTH_STATE_TTL_SECONDS = 10 * 60
SOCIAL_LIVE_CACHE_TTL_SECONDS = 60
SOCIAL_OAUTH_STATES = {}
SOCIAL_LIVE_CACHE = {}
SOCIAL_OAUTH_LOCK = threading.RLock()
UPLOAD_FOLDER = "UPLOADS"
UPLOAD_CATALOG_FILE = "uploads.json"
MAX_UPLOAD_FILES = 10
MAX_UPLOAD_FILE_BYTES = 192 * 1024 * 1024
MAX_UPLOAD_TOTAL_BYTES = 256 * 1024 * 1024
ALLOWED_UPLOAD_EXTENSIONS = {
    ".mcaddon", ".mcpack", ".mcworld", ".mctemplate", ".mcfunction",
    ".mcstructure", ".mcskin", ".zip", ".schem", ".litematic",
    ".json", ".png", ".txt", ".jpg", ".jar",
}
MAX_WATCHED_ITEMS = 1200
MAX_CONTINUE_ITEMS = 600
MIN_PROGRESS_SECONDS = 15
WATCHED_PROGRESS_THRESHOLD = 0.9
MINECRAFT_REQUEST_TIMEOUT = 150
MINECRAFT_CACHE_TTL_SECONDS = 900
MINECRAFT_PROFILE_CACHE = {}
MINECRAFT_TEXTURE_CACHE = {}
MINECRAFT_USERNAME_PATTERN = re.compile(r"^[A-Za-z0-9_]{3,16}$")
YOUTUBE_RESULT_LIMIT = 1000
YOUTUBE_REQUEST_TIMEOUT = 120
YOUTUBE_CACHE_TTL_SECONDS = 6000
YOUTUBE_SEARCH_CACHE = {}
YOUTUBE_RANDOM_QUERIES = [
    "cinematic short film",
    "funny animal videos",
    "space documentary",
    "travel vlog",
    "relaxing piano music",
    "live concert",
    "science experiments",
    "retro game review",
    "epic movie trailer",
    "nature in 4k",
    "coding project build",
    "street food tour",
    "basketball highlights",
    "history documentary",
    "drone footage mountains",
    "car restoration",
    "Anime",
    "Dennome",
    "Arazhul",
    "Roblox",
    "Chaosflo44",
    "RTXgamer180",
    "Kai_Cenat"
]


def get_media_root():
    root = os.path.abspath(MOVIE_FOLDER)
    os.makedirs(root, exist_ok=True)
    return root


def safe_media_path(name):
    root = get_media_root()
    path = os.path.abspath(os.path.join(root, name))

    if path != root and not path.startswith(root + os.sep):
        return None

    return path


def humanize_title(name):
    title = name
    for prefix in TEXT_LINK_PREFIXES:
        if title.lower().startswith(prefix):
            title = title[len(prefix):]
            break

    title = title.replace("_", " ").strip()
    return title or name


def read_text(path):
    with open(path, "r", encoding="utf-8") as handle:
        return handle.read().strip()


def read_title_for_base(base):
    title_path = safe_media_path(f"title_{base}.txt")
    if title_path and os.path.exists(title_path):
        title = read_text(title_path)
        if title:
            return title

    return humanize_title(base)


def find_logo(base):
    for ext in LOGO_EXTENSIONS:
        file_name = f"Logo_{base}{ext}"
        file_path = safe_media_path(file_name)
        if file_path and os.path.exists(file_path):
            return file_name
    return None


def fetch_remote_bytes(url, timeout, headers=None, data=None):
    request_headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/126.0 Safari/537.36"
        ),
        **(headers or {}),
    }
    request = urllib.request.Request(url, headers=request_headers, data=data)

    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read()


def fetch_remote_json(url, timeout, headers=None, data=None):
    payload = fetch_remote_bytes(url, timeout=timeout, headers=headers, data=data)
    return json.loads(payload.decode("utf-8"))


def read_link_target(path):
    contents = read_text(path)

    for line in contents.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.upper().startswith("URL="):
            return stripped.split("=", 1)[1].strip()

    for line in contents.splitlines():
        stripped = line.strip()
        if stripped:
            return stripped

    return ""


def youtube_thumbnail_url(video_id):
    return f"https://i.ytimg.com/vi/{video_id}/hqdefault.jpg"


def youtube_embed_url(video_id):
    return (
        f"https://www.youtube-nocookie.com/embed/{video_id}"
        "?autoplay=1&rel=0&modestbranding=1&playsinline=1&enablejsapi=1"
    )


def extract_youtube_id(url):
    parsed = urllib.parse.urlparse(url)
    host = parsed.netloc.lower().split(":")[0]
    host = host.removeprefix("www.")
    host = host.removeprefix("m.")

    if host == "youtu.be":
        video_id = parsed.path.strip("/").split("/", 1)[0]
        return video_id or None

    if host not in {"youtube.com", "youtube-nocookie.com"}:
        return None

    if parsed.path == "/watch":
        video_id = urllib.parse.parse_qs(parsed.query).get("v", [""])[0]
        return video_id or None

    parts = [part for part in parsed.path.split("/") if part]
    if len(parts) >= 2 and parts[0] in {"embed", "shorts", "live"}:
        return parts[1]

    return None


def build_local_item(file_name):
    base = Path(file_name).stem
    preview_name = f"preview_{base}.mp4"
    preview_path = safe_media_path(preview_name)

    return {
        "kind": "local",
        "file": file_name,
        "title": read_title_for_base(base),
        "preview": preview_name if preview_path and os.path.exists(preview_path) else None,
        "logo": find_logo(base),
        "thumbnail": None,
        "embedUrl": None,
        "videoId": None,
        "sourceLabel": "Local",
        "description": None,
    }


def build_youtube_result_item(video_id, title, source_label, description):
    return {
        "kind": "youtube",
        "file": None,
        "title": title,
        "preview": None,
        "logo": None,
        "thumbnail": youtube_thumbnail_url(video_id),
        "embedUrl": youtube_embed_url(video_id),
        "videoId": video_id,
        "sourceLabel": source_label,
        "description": description or "Opens in the embedded YouTube player.",
    }


def build_youtube_item(file_name):
    path = safe_media_path(file_name)
    if not path or not os.path.exists(path):
        return None

    url = read_link_target(path)
    video_id = extract_youtube_id(url)
    if not video_id:
        return None

    base = Path(file_name).stem
    item = build_youtube_result_item(
        video_id=video_id,
        title=read_title_for_base(base),
        source_label="Saved YouTube",
        description="Saved to the library from a YouTube link file.",
    )
    logo = find_logo(base)
    if logo:
        item["logo"] = logo

    return item


def get_movies():
    movies = []
    root = get_media_root()

    for file_name in sorted(os.listdir(root), key=str.lower):
        full_path = os.path.join(root, file_name)
        if not os.path.isfile(full_path):
            continue

        suffix = Path(file_name).suffix.lower()
        stem = Path(file_name).stem

        if suffix in VIDEO_EXTENSIONS and not file_name.lower().startswith("preview_"):
            movies.append(build_local_item(file_name))
            continue

        is_text_link = suffix == ".txt" and stem.lower().startswith(TEXT_LINK_PREFIXES)
        is_supported_link = suffix in LINK_EXTENSIONS or is_text_link

        if is_supported_link and not stem.lower().startswith(("title_", "logo_", "preview_")):
            item = build_youtube_item(file_name)
            if item:
                movies.append(item)

    movies.sort(key=lambda item: (item["title"].lower(), item["kind"]))
    return movies


def extract_text(node):
    if isinstance(node, str):
        return node.strip()

    if isinstance(node, list):
        text = "".join(part for part in (extract_text(item) for item in node) if part)
        return text.strip()

    if isinstance(node, dict):
        if "simpleText" in node:
            return str(node["simpleText"]).strip()
        if "runs" in node:
            text = "".join(part for part in (extract_text(item) for item in node["runs"]) if part)
            return text.strip()
        if "text" in node:
            return str(node["text"]).strip()

    return ""


def extract_balanced_json(text, start_index):
    depth = 0
    in_string = False
    escaped = False

    for index in range(start_index, len(text)):
        char = text[index]

        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue

        if char == '"':
            in_string = True
            continue

        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return text[start_index:index + 1]

    raise ValueError("Could not extract balanced JSON block.")


def parse_youtube_initial_data(html):
    markers = [
        "var ytInitialData = ",
        'window["ytInitialData"] = ',
        "ytInitialData = ",
    ]

    for marker in markers:
        marker_index = html.find(marker)
        if marker_index == -1:
            continue

        json_start = html.find("{", marker_index)
        if json_start == -1:
            continue

        payload = extract_balanced_json(html, json_start)
        return json.loads(payload)

    raise ValueError("Could not find YouTube search payload.")


def iter_video_renderers(node):
    if isinstance(node, dict):
        for key, value in node.items():
            if key == "videoRenderer" and isinstance(value, dict):
                yield value
            else:
                yield from iter_video_renderers(value)
    elif isinstance(node, list):
        for item in node:
            yield from iter_video_renderers(item)


def build_youtube_description(renderer):
    channel = extract_text(renderer.get("ownerText")) or extract_text(renderer.get("shortBylineText"))
    length = extract_text(renderer.get("lengthText"))
    views = extract_text(renderer.get("viewCountText")) or extract_text(renderer.get("shortViewCountText"))
    published = extract_text(renderer.get("publishedTimeText"))

    parts = [part for part in [channel, length, views, published] if part]
    return " | ".join(parts) if parts else "Found on YouTube."


def fetch_youtube_search_results(query, limit=YOUTUBE_RESULT_LIMIT, source_label="YouTube Search"):
    normalized_query = query.strip()
    if not normalized_query:
        return []

    cache_key = (normalized_query.lower(), limit, source_label)
    cached = YOUTUBE_SEARCH_CACHE.get(cache_key)
    if cached and (time.time() - cached["timestamp"]) < YOUTUBE_CACHE_TTL_SECONDS:
        return cached["items"]

    url = "https://www.youtube.com/results?" + urllib.parse.urlencode({"search_query": normalized_query})
    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/125.0 Safari/537.36"
            ),
            "Accept-Language": "en-US,en;q=0.9",
        },
    )

    with urllib.request.urlopen(request, timeout=YOUTUBE_REQUEST_TIMEOUT) as response:
        html = response.read().decode("utf-8", errors="ignore")

    data = parse_youtube_initial_data(html)

    results = []
    seen_video_ids = set()

    for renderer in iter_video_renderers(data):
        video_id = renderer.get("videoId")
        if not video_id or video_id in seen_video_ids:
            continue

        title = extract_text(renderer.get("title")) or "Untitled YouTube video"
        description = build_youtube_description(renderer)
        results.append(build_youtube_result_item(video_id, title, source_label, description))
        seen_video_ids.add(video_id)

        if len(results) >= limit:
            break

    YOUTUBE_SEARCH_CACHE[cache_key] = {
        "timestamp": time.time(),
        "items": results,
    }
    return results


def get_random_youtube_results(limit=YOUTUBE_RESULT_LIMIT):
    queries = random.sample(YOUTUBE_RANDOM_QUERIES, k=min(len(YOUTUBE_RANDOM_QUERIES), 6))
    last_error = None

    for query in queries:
        try:
            items = fetch_youtube_search_results(query, limit=limit, source_label="Random YouTube")
        except Exception as error:
            last_error = error
            continue

        if items:
            return query, items

    if last_error:
        raise last_error

    return random.choice(YOUTUBE_RANDOM_QUERIES), []


def get_local_ip():
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        sock.connect(("8.8.8.8", 80))
        ip = sock.getsockname()[0]
    except Exception:
        ip = "127.0.0.1"
    finally:
        sock.close()
    return ip


def get_account_root():
    return "__db__/accounts"


def sanitize_account_key(account_key):
    safe_key = "".join(
        char if char.isalnum() or char in "._-" else "_"
        for char in str(account_key or "unknown")
    )
    return safe_key or "unknown"


def sanitize_playlist_name(name):
    return " ".join(str(name or "").split()).strip()[:80]


def get_account_paths(account_key):
    safe_key = sanitize_account_key(account_key)
    account_folder = os.path.join(get_account_root(), safe_key)
    return {
        "accountKey": safe_key,
        "username": os.path.join(get_account_root(), f"{safe_key}.txt"),
        "folder": account_folder,
        "watched": os.path.join(account_folder, WATCHED_FILE_NAME),
        "continue": os.path.join(account_folder, CONTINUE_FILE_NAME),
        "playlists": os.path.join(account_folder, PLAYLISTS_FILE_NAME),
        "minecraft": os.path.join(account_folder, MINECRAFT_PROFILE_FILE_NAME),
        "socials": os.path.join(account_folder, SOCIALS_FILE_NAME),
    }


def init_database():
    os.makedirs(os.path.dirname(DATABASE_FILE), exist_ok=True)
    with DATABASE_LOCK, sqlite3.connect(DATABASE_FILE) as connection:
        connection.execute("PRAGMA journal_mode=WAL")
        connection.execute("PRAGMA foreign_keys=ON")
        connection.execute(
            """CREATE TABLE IF NOT EXISTS app_data (
                data_key TEXT PRIMARY KEY,
                data_json TEXT NOT NULL,
                updated_at INTEGER NOT NULL
            )"""
        )
        connection.execute(
            """CREATE TABLE IF NOT EXISTS binary_data (
                storage_key TEXT PRIMARY KEY,
                file_name TEXT NOT NULL,
                content_type TEXT NOT NULL,
                data BLOB NOT NULL,
                size INTEGER NOT NULL,
                updated_at INTEGER NOT NULL
            )"""
        )
        connection.commit()


init_database()

def _db_key(path):
    return os.path.normcase(os.path.abspath(str(path)))


def _db_get(path):
    init_database()
    key = _db_key(path)
    with DATABASE_LOCK, sqlite3.connect(DATABASE_FILE) as connection:
        row = connection.execute(
            "SELECT data_json FROM app_data WHERE data_key = ?", (key,)
        ).fetchone()
    if not row:
        return None
    try:
        return json.loads(row[0])
    except (TypeError, json.JSONDecodeError):
        return None


def _db_set(path, payload):
    init_database()
    key = _db_key(path)
    encoded = json.dumps(payload, ensure_ascii=False, separators=(",", ":"))
    with DATABASE_LOCK, sqlite3.connect(DATABASE_FILE) as connection:
        connection.execute(
            """INSERT INTO app_data(data_key, data_json, updated_at)
               VALUES(?, ?, ?)
               ON CONFLICT(data_key) DO UPDATE SET
                   data_json = excluded.data_json,
                   updated_at = excluded.updated_at""",
            (key, encoded, int(time.time())),
        )
        connection.commit()


def _blob_key(name):
    return str(name or "").replace("\\", "/").strip("/")


def _blob_set(storage_key, file_name, content_type, payload):
    init_database()
    key = _blob_key(storage_key)
    data = bytes(payload or b"")
    with DATABASE_LOCK, sqlite3.connect(DATABASE_FILE) as connection:
        connection.execute(
            """INSERT INTO binary_data(storage_key, file_name, content_type, data, size, updated_at)
               VALUES(?, ?, ?, ?, ?, ?)
               ON CONFLICT(storage_key) DO UPDATE SET
                   file_name=excluded.file_name, content_type=excluded.content_type,
                   data=excluded.data, size=excluded.size, updated_at=excluded.updated_at""",
            (key, str(file_name or ""), str(content_type or "application/octet-stream"), sqlite3.Binary(data), len(data), int(time.time())),
        )
        connection.commit()
    return key


def _blob_get(storage_key):
    init_database()
    with DATABASE_LOCK, sqlite3.connect(DATABASE_FILE) as connection:
        row = connection.execute(
            "SELECT file_name, content_type, data, size FROM binary_data WHERE storage_key = ?",
            (_blob_key(storage_key),),
        ).fetchone()
    if not row:
        return None
    return {"file_name": row[0], "content_type": row[1], "data": bytes(row[2]), "size": int(row[3] or 0)}


def _blob_exists(storage_key):
    init_database()
    with DATABASE_LOCK, sqlite3.connect(DATABASE_FILE) as connection:
        row = connection.execute("SELECT 1 FROM binary_data WHERE storage_key = ?", (_blob_key(storage_key),)).fetchone()
    return bool(row)


def _blob_delete(storage_key):
    init_database()
    with DATABASE_LOCK, sqlite3.connect(DATABASE_FILE) as connection:
        connection.execute("DELETE FROM binary_data WHERE storage_key = ?", (_blob_key(storage_key),))
        connection.commit()


def _blob_list(prefix):
    init_database()
    prefix = _blob_key(prefix)
    with DATABASE_LOCK, sqlite3.connect(DATABASE_FILE) as connection:
        return connection.execute(
            "SELECT storage_key, file_name, content_type, size FROM binary_data WHERE storage_key LIKE ?",
            (prefix.rstrip("/") + "/%",),
        ).fetchall()


def _migrate_json_file_to_database(path, default):
    if not os.path.exists(path):
        return default
    try:
        with open(path, "r", encoding="utf-8") as handle:
            data = json.load(handle)
    except (OSError, json.JSONDecodeError):
        return default
    if not isinstance(data, type(default)):
        return default
    _db_set(path, data)
    try:
        os.replace(path, path + ".migrated")
    except OSError:
        pass
    return data


def read_json_file(path, default):
    data = _db_get(path)
    if data is not None and isinstance(data, type(default)):
        return data
    return _migrate_json_file_to_database(path, default)


def write_json_file(path, payload):
    _db_set(path, payload)


def get_auth_root():
    return "__db__/auth"


def get_users_path():
    return os.path.join(get_auth_root(), USERS_FILE_NAME)


def get_profile_picture_root():
    return "__db__/profile_pictures"


def get_chat_root():
    return "__db__/chat"


def canonical_username(username):
    return str(username or "").strip().lower()


def validate_username(username):
    clean_username = str(username or "").strip()
    if not USERNAME_PATTERN.fullmatch(clean_username):
        raise ValueError("Use a unique username with 3-20 letters, numbers, or underscores.")
    return clean_username


def read_users():
    users = read_json_file(get_users_path(), [])
    return users if isinstance(users, list) else []


def find_user(username):
    key = canonical_username(username)
    if not key:
        return None
    with AUTH_LOCK:
        for user in read_users():
            if isinstance(user, dict) and canonical_username(user.get("username")) == key:
                return user
    return None


def safe_profile_picture_path(name):
    clean_name = os.path.basename(str(name or ""))
    if not clean_name or clean_name != str(name or ""):
        return None
    return f"{get_profile_picture_root()}/{clean_name}"


def public_user(user):
    if not isinstance(user, dict):
        return None
    username = str(user.get("username") or "").strip()
    if not username:
        return None
    picture_name = str(user.get("profilePicture") or "")
    picture_path = safe_profile_picture_path(picture_name) if picture_name else None
    return {
        "username": username,
        "profilePictureUrl": "/profile/picture/" + urllib.parse.quote(picture_name) if picture_path and _blob_exists(picture_path) else "",
        "createdAt": int(user.get("createdAt") or 0),
    }


def hash_password(password):
    clean_password = str(password or "")
    if len(clean_password) < 8:
        raise ValueError("Use a password with at least 8 characters.")
    if len(clean_password) > 200:
        raise ValueError("Password is too long.")
    salt = secrets.token_bytes(16)
    derived = hashlib.scrypt(clean_password.encode("utf-8"), salt=salt, n=2**14, r=8, p=1, dklen=32)
    return "scrypt$" + base64.b64encode(salt).decode("ascii") + "$" + base64.b64encode(derived).decode("ascii")


def verify_password(password, password_hash):
    try:
        algorithm, salt_text, hash_text = str(password_hash or "").split("$", 2)
        if algorithm != "scrypt":
            return False
        salt = base64.b64decode(salt_text.encode("ascii"), validate=True)
        expected = base64.b64decode(hash_text.encode("ascii"), validate=True)
        actual = hashlib.scrypt(str(password or "").encode("utf-8"), salt=salt, n=2**14, r=8, p=1, dklen=len(expected))
        return hmac.compare_digest(actual, expected)
    except (ValueError, TypeError):
        return False


def register_user(username, password):
    clean_username = validate_username(username)
    key = canonical_username(clean_username)
    with AUTH_LOCK:
        users = read_users()
        if any(isinstance(user, dict) and canonical_username(user.get("username")) == key for user in users):
            raise ValueError("That username is already taken.")
        user = {"username": clean_username, "passwordHash": hash_password(password), "profilePicture": "", "createdAt": int(time.time())}
        users.append(user)
        write_json_file(get_users_path(), users)
    create_account(clean_username, clean_username)
    return user


def migrate_legacy_storage_to_database():
    """Move legacy NotFlix storage into SQLite while keeping MOVIES_DC1 untouched."""
    init_database()

    # Convert old app_data keys (which used real folder paths) to the new logical DB namespaces.
    legacy_prefixes = {
        os.path.abspath(ACCOUNT_FOLDER): get_account_root(),
        os.path.abspath(AUTH_FOLDER): get_auth_root(),
        os.path.abspath(CHAT_FOLDER): get_chat_root(),
        os.path.abspath(DRAWINGS_FOLDER): get_drawings_root(),
        os.path.abspath(FEEDBACK_FOLDER): get_feedback_root(),
        os.path.abspath(UPLOAD_FOLDER): get_upload_root(),
    }
    with DATABASE_LOCK, sqlite3.connect(DATABASE_FILE) as connection:
        rows = connection.execute("SELECT data_key, data_json, updated_at FROM app_data").fetchall()
        for old_key, data_json, updated_at in rows:
            normalized_old = os.path.normcase(os.path.abspath(old_key))
            new_key = None
            for old_root, new_root in legacy_prefixes.items():
                old_root_norm = os.path.normcase(old_root)
                if normalized_old == old_root_norm:
                    new_key = new_root
                    break
                prefix = old_root_norm + os.sep
                if normalized_old.startswith(prefix):
                    relative = normalized_old[len(prefix):].replace(os.sep, "/")
                    new_key = new_root.rstrip("/") + "/" + relative
                    break
            if new_key:
                connection.execute(
                    """INSERT INTO app_data(data_key, data_json, updated_at) VALUES(?, ?, ?)
                       ON CONFLICT(data_key) DO NOTHING""",
                    (new_key, data_json, updated_at),
                )
        connection.commit()

    # Import legacy JSON/text files that may predate the database-backed version.
    for root_name in [ACCOUNT_FOLDER, AUTH_FOLDER, CHAT_FOLDER, DRAWINGS_FOLDER, FEEDBACK_FOLDER, UPLOAD_FOLDER]:
        root = Path(root_name)
        if not root.exists() or not root.is_dir():
            continue
        for file_path in root.rglob("*"):
            if not file_path.is_file():
                continue
            try:
                relative = file_path.relative_to(root).as_posix()
                if root_name == ACCOUNT_FOLDER:
                    key = f"{get_account_root()}/{relative}"
                elif root_name == AUTH_FOLDER:
                    key = f"{get_auth_root()}/{relative}"
                elif root_name == CHAT_FOLDER:
                    key = f"{get_chat_root()}/{relative}"
                elif root_name == DRAWINGS_FOLDER:
                    key = f"{get_drawings_root()}/{relative}"
                elif root_name == FEEDBACK_FOLDER:
                    key = f"{get_feedback_root()}/{relative}"
                else:
                    key = f"{get_upload_root()}/{relative}"

                if file_path.suffix.lower() == ".json":
                    try:
                        payload = json.loads(file_path.read_text(encoding="utf-8"))
                        _db_set(key, payload)
                    except (OSError, json.JSONDecodeError):
                        pass
                elif root_name == ACCOUNT_FOLDER and file_path.suffix.lower() == ".txt":
                    try:
                        _db_set(key, file_path.read_text(encoding="utf-8").strip())
                    except OSError:
                        pass
            except OSError:
                pass

    # Import old binary files into SQLite BLOB storage.
    for root_name in [PROFILE_PICTURE_FOLDER, DRAWINGS_FOLDER, UPLOAD_FOLDER]:
        root = Path(root_name)
        if not root.exists() or not root.is_dir():
            continue
        for file_path in root.rglob("*"):
            if not file_path.is_file() or file_path.suffix.lower() in {".json", ".migrated"}:
                continue
            try:
                payload = file_path.read_bytes()
                rel = file_path.relative_to(root).as_posix()
                if root_name == PROFILE_PICTURE_FOLDER:
                    storage_key = f"{get_profile_picture_root()}/{rel}"
                elif root_name == DRAWINGS_FOLDER:
                    storage_key = f"{get_drawings_root()}/{rel}"
                else:
                    storage_key = f"{get_upload_root()}/{rel}"
                _blob_set(storage_key, file_path.name, mimetypes.guess_type(file_path.name)[0] or "application/octet-stream", payload)
            except OSError:
                continue

    # Delete only legacy application-data folders. MOVIES_DC1 is deliberately preserved.
    for root_name in [ACCOUNT_FOLDER, AUTH_FOLDER, CHAT_FOLDER, PROFILE_PICTURE_FOLDER, DRAWINGS_FOLDER, FEEDBACK_FOLDER, UPLOAD_FOLDER]:
        root = Path(root_name)
        if root.exists() and root.is_dir():
            try:
                import shutil
                shutil.rmtree(root)
            except OSError:
                pass


def ensure_feedback_admin_account():
    """Create the built-in feedback manager account if it does not exist."""
    username = ADMIN_FEEDBACK_USERNAME
    if find_user(username):
        return
    password = str(RAPHUZ_BOOTSTRAP_PASSWORD or "").strip()
    if len(password) < 8:
        raise RuntimeError("NOTFLIX_RAPHUZ_PASSWORD must contain at least 8 characters.")
    with AUTH_LOCK:
        users = read_users()
        if any(isinstance(user, dict) and canonical_username(user.get("username")) == canonical_username(username) for user in users):
            return
        users.append({"username": username, "passwordHash": hash_password(password), "profilePicture": "", "createdAt": int(time.time()), "role": "feedback_admin"})
        write_json_file(get_users_path(), users)
    create_account(username, username)


def create_session(username):
    token = secrets.token_urlsafe(32)
    with AUTH_LOCK:
        SESSIONS[token] = {
            "username": canonical_username(username),
            "expiresAt": int(time.time()) + SESSION_TTL_SECONDS,
            "csrfToken": secrets.token_urlsafe(32),
        }
    return token


def get_session_csrf_token(token):
    with AUTH_LOCK:
        session = SESSIONS.get(token)
        if not session or int(session.get("expiresAt") or 0) <= int(time.time()):
            return ""
        return str(session.get("csrfToken") or "")


def get_session_username(token):
    if not token:
        return ""
    with AUTH_LOCK:
        session = SESSIONS.get(token)
        if not session or int(session.get("expiresAt") or 0) <= int(time.time()):
            SESSIONS.pop(token, None)
            return ""
        return str(session.get("username") or "")


def remove_session(token):
    with AUTH_LOCK:
        SESSIONS.pop(token, None)


def update_profile_picture(username, file_data):
    filename = os.path.basename(str(file_data.get("filename") or ""))
    extension = os.path.splitext(filename)[1].lower()
    content = file_data.get("content") or b""
    if extension not in PROFILE_PICTURE_EXTENSIONS:
        raise ValueError("Use a PNG, JPG, WEBP, or GIF profile picture.")
    if not content or len(content) > MAX_PROFILE_PICTURE_BYTES:
        raise ValueError("Profile pictures must be between 1 byte and 2 MB.")
    stored_name = uuid.uuid4().hex + extension
    stored_path = safe_profile_picture_path(stored_name)
    if not stored_path:
        raise ValueError("Could not prepare the profile picture.")
    _blob_set(stored_path, stored_name, mimetypes.guess_type(stored_name)[0] or "application/octet-stream", content)

    old_picture = ""
    with AUTH_LOCK:
        users = read_users()
        for user in users:
            if isinstance(user, dict) and canonical_username(user.get("username")) == canonical_username(username):
                old_picture = str(user.get("profilePicture") or "")
                user["profilePicture"] = stored_name
                break
        write_json_file(get_users_path(), users)

    old_path = safe_profile_picture_path(old_picture) if old_picture else None
    if old_path:
        _blob_delete(old_path)
    return public_user(find_user(username))


def clean_chat_text(text):
    clean_text = " ".join(str(text or "").replace("\r", " ").replace("\n", " ").split())
    if not clean_text:
        raise ValueError("Write a message first.")
    if len(clean_text) > MAX_CHAT_MESSAGE_LENGTH:
        raise ValueError(f"Messages can be up to {MAX_CHAT_MESSAGE_LENGTH} characters.")
    return clean_text


def public_chat_message(record):
    sender_user = public_user(find_user(record.get("sender"))) or {"username": str(record.get("sender") or "Member"), "profilePictureUrl": ""}
    return {
        "id": str(record.get("id") or ""),
        "sender": sender_user["username"],
        "senderPictureUrl": sender_user["profilePictureUrl"],
        "recipient": str(record.get("recipient") or ""),
        "text": str(record.get("text") or ""),
        "createdAt": int(record.get("createdAt") or 0),
    }


def read_messages(path):
    messages = read_json_file(path, [])
    return messages if isinstance(messages, list) else []


def list_global_messages():
    path = os.path.join(get_chat_root(), GLOBAL_CHAT_FILE_NAME)
    with CHAT_LOCK:
        messages = read_messages(path)[-100:]
    return [public_chat_message(message) for message in messages]


def send_global_message(username, text):
    user = find_user(username)
    message = {"id": uuid.uuid4().hex, "sender": user["username"], "text": clean_chat_text(text), "createdAt": int(time.time())}
    path = os.path.join(get_chat_root(), GLOBAL_CHAT_FILE_NAME)
    with CHAT_LOCK:
        messages = read_messages(path)
        messages.append(message)
        write_json_file(path, messages[-MAX_GLOBAL_CHAT_MESSAGES:])
    return public_chat_message(message)


def direct_chat_path(first_username, second_username):
    pair = "::".join(sorted([canonical_username(first_username), canonical_username(second_username)]))
    root = os.path.join(get_chat_root(), DIRECT_CHAT_FOLDER)
    return os.path.join(root, hashlib.sha256(pair.encode("utf-8")).hexdigest() + ".json")


def list_direct_messages(username, other_username):
    other = find_user(other_username)
    if not other:
        raise ValueError("That user does not exist.")
    with CHAT_LOCK:
        messages = read_messages(direct_chat_path(username, other["username"]))[-100:]
    return [public_chat_message(message) for message in messages]


def send_direct_message(username, recipient, text):
    sender = find_user(username)
    other = find_user(recipient)
    if not sender or not other:
        raise ValueError("That user does not exist.")
    if canonical_username(sender["username"]) == canonical_username(other["username"]):
        raise ValueError("Choose another user for a direct message.")
    message = {"id": uuid.uuid4().hex, "sender": sender["username"], "recipient": other["username"], "text": clean_chat_text(text), "createdAt": int(time.time())}
    path = direct_chat_path(sender["username"], other["username"])
    with CHAT_LOCK:
        messages = read_messages(path)
        messages.append(message)
        write_json_file(path, messages[-MAX_DIRECT_CHAT_MESSAGES:])
    return public_chat_message(message)


def list_public_users(exclude_username=""):
    excluded = canonical_username(exclude_username)
    with AUTH_LOCK:
        users = [public_user(user) for user in read_users()]
    result = []
    for user in users:
        if not user or canonical_username(user["username"]) == excluded:
            continue
        socials = refresh_public_socials(user["username"])
        user["socials"] = socials
        result.append(user)
    return sorted(result, key=lambda user: user["username"].lower())


def get_upload_root():
    return "__db__/uploads"


def get_upload_catalog_path():
    return os.path.join(get_upload_root(), UPLOAD_CATALOG_FILE)


def safe_upload_path(name):
    clean_name = os.path.basename(str(name or ""))
    if not clean_name or clean_name != str(name or ""):
        return None
    return f"{get_upload_root()}/{clean_name}"


def sanitize_upload_filename(name):
    clean_name = os.path.basename(str(name or "").strip())
    if not clean_name or clean_name != str(name or "").strip():
        raise ValueError("Upload files need a valid filename.")

    extension = os.path.splitext(clean_name)[1].lower()
    if extension not in ALLOWED_UPLOAD_EXTENSIONS:
        allowed = ", ".join(sorted(ALLOWED_UPLOAD_EXTENSIONS))
        raise ValueError(f"Unsupported file type. Allowed: {allowed}.")

    return clean_name, extension


def sanitize_upload_text(value, limit):
    return " ".join(str(value or "").split()).strip()[:limit]


def parse_upload_price(value):
    raw_value = str(value or "").strip().replace(",", ".")
    if not raw_value:
        return 0

    try:
        amount = Decimal(raw_value)
    except InvalidOperation as error:
        raise ValueError("Enter a valid price, for example 2.50.") from error

    if not amount.is_finite() or amount < 0 or amount > Decimal("9999.99"):
        raise ValueError("Price must be between 0 and 9999.99.")

    return int((amount * 100).quantize(Decimal("1"), rounding=ROUND_HALF_UP))


def format_upload_price(price_cents):
    cents = max(0, int(price_cents or 0))
    if cents == 0:
        return "Free"
    return f"€{cents / 100:.2f}"


def normalize_upload_record(raw):
    if not isinstance(raw, dict):
        return None

    upload_id = str(raw.get("id") or "").lower()
    storage_name = str(raw.get("storageName") or "")
    if not re.fullmatch(r"[a-f0-9]{32}", upload_id):
        return None

    try:
        original_name, extension = sanitize_upload_filename(raw.get("originalName") or storage_name)
    except ValueError:
        return None

    path = safe_upload_path(storage_name)
    blob = _blob_get(path) if path else None
    if not blob or blob["size"] > MAX_UPLOAD_FILE_BYTES:
        return None

    try:
        price_cents = parse_upload_price(Decimal(int(raw.get("priceCents") or 0)) / 100)
    except (ValueError, InvalidOperation, TypeError):
        price_cents = 0

    return {
        "id": upload_id,
        "storageName": storage_name,
        "originalName": original_name,
        "extension": extension,
        "title": sanitize_upload_text(raw.get("title"), 100) or humanize_title(os.path.splitext(original_name)[0]),
        "description": sanitize_upload_text(raw.get("description"), 600),
        "uploader": sanitize_upload_text(raw.get("uploader"), 80) or "NotFlix creator",
        "createdAt": int(raw.get("createdAt") or 0),
        "priceCents": price_cents,
        "size": int(blob["size"]),
    }


def read_upload_catalog():
    records = read_json_file(get_upload_catalog_path(), [])
    if not isinstance(records, list):
        return []

    normalized = []
    seen_ids = set()
    for raw in records:
        record = normalize_upload_record(raw)
        if not record or record["id"] in seen_ids:
            continue
        seen_ids.add(record["id"])
        normalized.append(record)

    normalized.sort(key=lambda record: record["createdAt"], reverse=True)
    return normalized


def public_upload_record(record):
    return {
        "id": record["id"],
        "originalName": record["originalName"],
        "extension": record["extension"],
        "title": record["title"],
        "description": record["description"],
        "uploader": record["uploader"],
        "createdAt": record["createdAt"],
        "priceCents": record["priceCents"],
        "priceLabel": format_upload_price(record["priceCents"]),
        "size": record["size"],
        "downloadUrl": "/uploads/download?id=" + urllib.parse.quote(record["id"]),
    }


def publish_uploads(files, fields, uploader):
    if not files:
        raise ValueError("Choose at least one file to publish.")
    if len(files) > MAX_UPLOAD_FILES:
        raise ValueError(f"Upload up to {MAX_UPLOAD_FILES} files at a time.")

    title = sanitize_upload_text(fields.get("title"), 100)
    description = sanitize_upload_text(fields.get("description"), 600)
    price_cents = parse_upload_price(fields.get("price"))
    catalog = read_upload_catalog()
    created = []
    created_paths = []

    try:
        for index, file_data in enumerate(files, start=1):
            original_name, extension = sanitize_upload_filename(file_data.get("filename"))
            payload = file_data.get("content") or b""
            if not payload:
                raise ValueError(f"{original_name} is empty.")
            if len(payload) > MAX_UPLOAD_FILE_BYTES:
                raise ValueError(f"{original_name} is larger than the {MAX_UPLOAD_FILE_BYTES // (1024 * 1024)} MB file limit.")

            upload_id = uuid.uuid4().hex
            storage_name = upload_id + extension
            storage_path = safe_upload_path(storage_name)
            if not storage_path:
                raise ValueError("Could not prepare the upload destination.")

            _blob_set(storage_path, storage_name, mimetypes.guess_type(storage_name)[0] or "application/octet-stream", payload)
            created_paths.append(storage_path)

            display_title = title
            if not display_title:
                display_title = humanize_title(os.path.splitext(original_name)[0])
            elif len(files) > 1:
                display_title = f"{display_title} — {index}"

            record = {
                "id": upload_id,
                "storageName": storage_name,
                "originalName": original_name,
                "extension": extension,
                "title": display_title,
                "description": description,
                "uploader": uploader,
                "createdAt": int(time.time()),
                "priceCents": price_cents,
                "size": len(payload),
            }
            catalog.append(record)
            created.append(record)

        write_json_file(get_upload_catalog_path(), catalog)
    except Exception:
        for storage_path in created_paths:
            _blob_delete(storage_path)
        raise

    return [public_upload_record(record) for record in created]


def parse_multipart_form(content_type, raw_body):
    if "multipart/form-data" not in str(content_type or "").lower():
        raise ValueError("Upload requests must use multipart form data.")

    message = BytesParser(policy=EMAIL_POLICY).parsebytes(
        ("Content-Type: " + str(content_type) + "\r\nMIME-Version: 1.0\r\n\r\n").encode("utf-8")
        + raw_body
    )
    if not message.is_multipart():
        raise ValueError("The upload form was incomplete.")

    fields = {}
    files = []
    for part in message.iter_parts():
        if part.get_content_disposition() != "form-data":
            continue

        name = part.get_param("name", header="content-disposition")
        if not name:
            continue

        payload = part.get_payload(decode=True) or b""
        filename = part.get_filename()
        if filename:
            files.append({"filename": filename, "content": payload})
        else:
            fields[name] = payload.decode(part.get_content_charset() or "utf-8", errors="replace")

    return fields, files


def get_drawings_root():
    return "__db__/drawings"


def get_drawings_catalog_path():
    return os.path.join(get_drawings_root(), DRAWINGS_CATALOG_FILE)


def get_feedback_root():
    return "__db__/feedback"


def get_feedback_path():
    return os.path.join(get_feedback_root(), FEEDBACK_FILE_NAME)


def safe_drawing_path(name):
    clean = os.path.basename(str(name or ""))
    if not clean or clean != str(name or ""):
        return None
    return f"{get_drawings_root()}/{clean}"


def public_drawing(record):
    return {
        "id": str(record.get("id") or ""),
        "title": str(record.get("title") or "Untitled drawing"),
        "author": str(record.get("author") or "Member"),
        "file": str(record.get("file") or ""),
        "createdAt": int(record.get("createdAt") or 0),
    }


def list_drawings():
    records = read_json_file(get_drawings_catalog_path(), [])
    if not isinstance(records, list):
        records = []
    result = []
    for record in records[-200:]:
        if not isinstance(record, dict):
            continue
        path = safe_drawing_path(record.get("file"))
        if path and _blob_exists(path):
            result.append(public_drawing(record))
    return list(reversed(result))


def save_drawing(username, title, data_url):
    title = " ".join(str(title or "").split()).strip()[:MAX_DRAWING_TITLE] or "Untitled drawing"
    raw = str(data_url or "")
    if not raw.startswith("data:image/") or ";base64," not in raw:
        raise ValueError("The drawing image was invalid.")
    encoded = raw.split(";base64,", 1)[1]
    try:
        payload = base64.b64decode(encoded, validate=True)
    except Exception as error:
        raise ValueError("The drawing image could not be decoded.") from error
    if not payload or len(payload) > MAX_DRAWING_BYTES:
        raise ValueError("Drawings are limited to 900 KB each.")
    drawing_id = uuid.uuid4().hex
    filename = f"{drawing_id}.jpg"
    path = safe_drawing_path(filename)
    _blob_set(path, filename, "image/jpeg", payload)
    record = {"id": drawing_id, "title": title, "author": str(username), "file": filename, "createdAt": int(time.time())}
    catalog = read_json_file(get_drawings_catalog_path(), [])
    if not isinstance(catalog, list):
        catalog = []
    catalog.append(record)
    write_json_file(get_drawings_catalog_path(), catalog[-500:])
    return public_drawing(record)


def public_feedback(record):
    return {
        "id": str(record.get("id") or ""),
        "author": str(record.get("author") or "Member"),
        "message": str(record.get("message") or ""),
        "createdAt": int(record.get("createdAt") or 0),
        "bucketlisted": bool(record.get("bucketlisted")),
        "fixed": bool(record.get("fixed")),
        "status": str(record.get("status") or ("fixed" if record.get("fixed") else "open")),
    }


def list_feedback():
    records = read_json_file(get_feedback_path(), [])
    if not isinstance(records, list):
        records = []
    return [public_feedback(item) for item in reversed(records) if isinstance(item, dict)]


def submit_feedback(username, message):
    clean = str(message or "").strip()
    if not clean:
        raise ValueError("Please enter some feedback first.")
    if len(clean) > MAX_FEEDBACK_LENGTH:
        raise ValueError(f"Feedback is limited to {MAX_FEEDBACK_LENGTH} characters.")
    record = {"id": uuid.uuid4().hex, "author": str(username), "message": clean, "createdAt": int(time.time()), "bucketlisted": False, "fixed": False, "status": "open"}
    records = read_json_file(get_feedback_path(), [])
    if not isinstance(records, list):
        records = []
    records.append(record)
    write_json_file(get_feedback_path(), records[-2000:])
    return public_feedback(record)


def is_feedback_admin(username):
    return bool(username) and canonical_username(username) == canonical_username(ADMIN_FEEDBACK_USERNAME)


def update_feedback_admin(username, feedback_id, bucketlisted=None, fixed=None, status=None):
    if not is_feedback_admin(username):
        raise PermissionError("Only the Raphuz feedback account can manage the feedback board.")
    records = read_json_file(get_feedback_path(), [])
    if not isinstance(records, list):
        records = []
    target = next((item for item in records if isinstance(item, dict) and str(item.get("id")) == str(feedback_id)), None)
    if not target:
        raise ValueError("Feedback item not found.")
    if bucketlisted is not None:
        target["bucketlisted"] = bool(bucketlisted)
    if fixed is not None:
        target["fixed"] = bool(fixed)
    if status in {"open", "bucketlist", "in_progress", "fixed", "wont_fix"}:
        target["status"] = status
        target["fixed"] = status == "fixed"
    elif target.get("fixed"):
        target["status"] = "fixed"
    elif target.get("bucketlisted"):
        target["status"] = "bucketlist"
    else:
        target["status"] = "open"
    write_json_file(get_feedback_path(), records)
    return public_feedback(target)


def get_socials_key_path():
    return f"{get_account_root()}/_socials.key"


def get_socials_cipher():
    key_path = get_socials_key_path()
    stored = _blob_get(key_path)
    if stored:
        try:
            key = stored["data"].strip()
            Fernet(key)
            return Fernet(key)
        except (ValueError, TypeError):
            pass
    key = Fernet.generate_key()
    _blob_set(key_path, SOCIALS_KEY_FILE_NAME, "application/octet-stream", key)
    return Fernet(key)


def default_socials_state():
    return {
        "microsoft": {"linked": False, "displayName": "", "email": "", "accountId": "", "encryptedTokens": ""},
        "twitch": {"linked": False, "username": "", "displayName": "", "channelUrl": "", "live": False, "encryptedTokens": ""},
        "youtube": {"linked": False, "channelName": "", "channelUrl": "", "channelId": "", "live": False, "encryptedTokens": ""},
        "minecraft": {"java": "", "bedrock": ""},
    }


def load_socials_state(account_key):
    paths = get_account_paths(account_key)
    state = read_json_file(paths["socials"], default_socials_state())
    defaults = default_socials_state()
    if not isinstance(state, dict):
        state = defaults
    for key, value in defaults.items():
        if not isinstance(state.get(key), dict):
            state[key] = value.copy()
        else:
            for child_key, child_value in value.items():
                state[key].setdefault(child_key, child_value)
    return state


def public_socials_state(account_key):
    state = load_socials_state(account_key)
    public = default_socials_state()
    public["microsoft"] = {
        "linked": bool(state["microsoft"].get("linked")),
        "displayName": str(state["microsoft"].get("displayName") or ""),
    }
    public["twitch"] = {
        "linked": bool(state["twitch"].get("linked")),
        "username": str(state["twitch"].get("username") or ""),
        "displayName": str(state["twitch"].get("displayName") or ""),
        "channelUrl": str(state["twitch"].get("channelUrl") or ""),
        "live": bool(state["twitch"].get("live")),
    }
    public["youtube"] = {
        "linked": bool(state["youtube"].get("linked")),
        "channelName": str(state["youtube"].get("channelName") or ""),
        "channelUrl": str(state["youtube"].get("channelUrl") or ""),
        "channelId": str(state["youtube"].get("channelId") or ""),
        "live": bool(state["youtube"].get("live")),
    }
    legacy_java = load_minecraft_state(account_key).get("username") or ""
    public["minecraft"] = {
        "java": str(state["minecraft"].get("java") or legacy_java),
        "bedrock": str(state["minecraft"].get("bedrock") or ""),
    }
    return public


def save_socials_state(account_key, state):
    paths = get_account_paths(account_key)
    clean = default_socials_state()
    if isinstance(state, dict):
        for key in clean:
            if isinstance(state.get(key), dict):
                clean[key].update(state[key])
    write_json_file(paths["socials"], clean)
    return public_socials_state(account_key)


def encrypt_social_token(token):
    if not token:
        return ""
    return get_socials_cipher().encrypt(json.dumps(token, ensure_ascii=False).encode("utf-8")).decode("ascii")


def decrypt_social_token(value):
    if not value:
        return {}
    try:
        raw = get_socials_cipher().decrypt(str(value).encode("ascii")).decode("utf-8")
        data = json.loads(raw)
        return data if isinstance(data, dict) else {}
    except (InvalidToken, ValueError, UnicodeDecodeError, json.JSONDecodeError):
        return {}


def save_social_service(account_key, service, public_fields, tokens=None):
    state = load_socials_state(account_key)
    current = state.get(service, {}) if isinstance(state.get(service), dict) else {}
    current.update(public_fields or {})
    if tokens is not None:
        current["encryptedTokens"] = encrypt_social_token(tokens)
    state[service] = current
    return save_socials_state(account_key, state)


def get_social_tokens(account_key, service):
    state = load_socials_state(account_key)
    service_state = state.get(service, {}) if isinstance(state.get(service), dict) else {}
    return decrypt_social_token(service_state.get("encryptedTokens"))


def oauth_config(provider):
    if provider == "microsoft":
        return {
            "client_id": os.environ.get("NOTFLIX_MICROSOFT_CLIENT_ID", "").strip(),
            "client_secret": os.environ.get("NOTFLIX_MICROSOFT_CLIENT_SECRET", "").strip(),
        }
    if provider == "twitch":
        return {
            "client_id": os.environ.get("NOTFLIX_TWITCH_CLIENT_ID", "").strip(),
            "client_secret": os.environ.get("NOTFLIX_TWITCH_CLIENT_SECRET", "").strip(),
            "redirect_uri": os.environ.get("NOTFLIX_TWITCH_REDIRECT_URI", "").strip(),
        }
    if provider == "youtube":
        return {
            "client_id": os.environ.get("NOTFLIX_YOUTUBE_CLIENT_ID", "").strip(),
            "client_secret": os.environ.get("NOTFLIX_YOUTUBE_CLIENT_SECRET", "").strip(),
            "redirect_uri": os.environ.get("NOTFLIX_YOUTUBE_REDIRECT_URI", "").strip(),
        }
    return {}


def oauth_redirect_uri(handler, provider):
    config = oauth_config(provider)
    if config.get("redirect_uri"):
        return config["redirect_uri"]
    forwarded_proto = handler.headers.get("X-Forwarded-Proto", "").split(",", 1)[0].strip().lower()
    scheme = forwarded_proto if forwarded_proto in {"http", "https"} else "http"
    host = handler.headers.get("Host", f"localhost:{PORT}")
    return f"{scheme}://{host}/socials/{provider}/callback"


def http_form_request(url, fields, headers=None, timeout=30):
    body = urllib.parse.urlencode(fields).encode("utf-8")
    request = urllib.request.Request(url, data=body, headers={"Content-Type": "application/x-www-form-urlencoded", **(headers or {})}, method="POST")
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return json.loads(response.read().decode("utf-8"))


def http_json_request(url, headers=None, timeout=30):
    request = urllib.request.Request(url, headers=headers or {})
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return json.loads(response.read().decode("utf-8"))


def create_oauth_state(username, provider):
    state = secrets.token_urlsafe(32)
    with SOCIAL_OAUTH_LOCK:
        SOCIAL_OAUTH_STATES[state] = {"username": username, "provider": provider, "createdAt": time.time()}
        cutoff = time.time() - SOCIAL_OAUTH_STATE_TTL_SECONDS
        for key, value in list(SOCIAL_OAUTH_STATES.items()):
            if value.get("createdAt", 0) < cutoff:
                SOCIAL_OAUTH_STATES.pop(key, None)
    return state


def consume_oauth_state(state, provider):
    with SOCIAL_OAUTH_LOCK:
        record = SOCIAL_OAUTH_STATES.pop(str(state or ""), None)
    if not record or record.get("provider") != provider or time.time() - record.get("createdAt", 0) > SOCIAL_OAUTH_STATE_TTL_SECONDS:
        return ""
    return str(record.get("username") or "")


def microsoft_device_start(username):
    config = oauth_config("microsoft")
    if not config["client_id"]:
        raise ValueError("Microsoft linking is not configured. Set NOTFLIX_MICROSOFT_CLIENT_ID first.")
    data = http_form_request(
        "https://login.microsoftonline.com/consumers/oauth2/v2.0/devicecode",
        {"client_id": config["client_id"], "scope": "openid profile email User.Read offline_access"},
    )
    token_data = {"device_code": data.get("device_code"), "interval": int(data.get("interval") or 5), "expires_in": int(data.get("expires_in") or 900), "started_at": time.time()}
    save_social_service(username, "microsoft", {"linked": False, "displayName": "", "email": "", "accountId": ""}, {"device": token_data})
    return {"verificationUri": data.get("verification_uri") or data.get("verification_uri_complete") or "https://microsoft.com/devicelogin", "verificationUriComplete": data.get("verification_uri_complete") or "", "userCode": data.get("user_code") or "", "expiresIn": int(data.get("expires_in") or 900), "interval": int(data.get("interval") or 5)}


def microsoft_device_poll(username):
    config = oauth_config("microsoft")
    tokens = get_social_tokens(username, "microsoft")
    device = tokens.get("device") if isinstance(tokens, dict) else None
    if not config["client_id"] or not isinstance(device, dict) or not device.get("device_code"):
        raise ValueError("No Microsoft link request is waiting.")
    if time.time() - float(device.get("started_at") or 0) > float(device.get("expires_in") or 900):
        raise ValueError("The Microsoft sign-in code expired. Start linking again.")
    try:
        data = http_form_request("https://login.microsoftonline.com/consumers/oauth2/v2.0/token", {"grant_type": "urn:ietf:params:oauth:grant-type:device_code", "client_id": config["client_id"], "device_code": device["device_code"]})
    except urllib.error.HTTPError as error:
        try:
            body = json.loads(error.read().decode("utf-8"))
        except Exception:
            body = {}
        code = body.get("error")
        if code in {"authorization_pending", "slow_down"}:
            return {"pending": True, "retryAfter": 5 if code == "authorization_pending" else 10}
        raise ValueError(body.get("error_description") or "Microsoft sign-in could not be completed.")
    profile = http_json_request("https://graph.microsoft.com/v1.0/me", {"Authorization": "Bearer " + data.get("access_token", "")})
    public = {"linked": True, "displayName": profile.get("displayName") or profile.get("userPrincipalName") or "Microsoft account", "email": profile.get("mail") or profile.get("userPrincipalName") or "", "accountId": profile.get("id") or ""}
    data.pop("token_type", None)
    data["storedAt"] = int(time.time())
    save_social_service(username, "microsoft", public, data)
    return {"pending": False, "socials": public_socials_state(username)}


def build_twitch_auth_url(handler, username):
    config = oauth_config("twitch")
    if not config["client_id"] or not config["client_secret"]:
        raise ValueError("Twitch linking is not configured. Set NOTFLIX_TWITCH_CLIENT_ID and NOTFLIX_TWITCH_CLIENT_SECRET first.")
    state = create_oauth_state(username, "twitch")
    params = {"client_id": config["client_id"], "redirect_uri": oauth_redirect_uri(handler, "twitch"), "response_type": "code", "scope": "user:read:email", "state": state}
    return "https://id.twitch.tv/oauth2/authorize?" + urllib.parse.urlencode(params)


def finish_twitch_oauth(handler, code, state):
    username = consume_oauth_state(state, "twitch")
    if not username:
        raise ValueError("The Twitch sign-in session expired. Start linking again.")
    config = oauth_config("twitch")
    data = http_form_request("https://id.twitch.tv/oauth2/token", {"client_id": config["client_id"], "client_secret": config["client_secret"], "code": code, "grant_type": "authorization_code", "redirect_uri": oauth_redirect_uri(handler, "twitch")})
    profile = http_json_request("https://api.twitch.tv/helix/users", {"Authorization": "Bearer " + data.get("access_token", ""), "Client-Id": config["client_id"]})
    user = (profile.get("data") or [{}])[0]
    public = {"linked": True, "username": user.get("login") or "", "displayName": user.get("display_name") or user.get("login") or "", "channelUrl": "https://www.twitch.tv/" + str(user.get("login") or ""), "live": False}
    data["storedAt"] = int(time.time())
    save_social_service(username, "twitch", public, data)
    return username


def build_youtube_auth_url(handler, username):
    config = oauth_config("youtube")
    if not config["client_id"] or not config["client_secret"]:
        raise ValueError("YouTube linking is not configured. Set NOTFLIX_YOUTUBE_CLIENT_ID and NOTFLIX_YOUTUBE_CLIENT_SECRET first.")
    state = create_oauth_state(username, "youtube")
    params = {"client_id": config["client_id"], "redirect_uri": oauth_redirect_uri(handler, "youtube"), "response_type": "code", "scope": "https://www.googleapis.com/auth/youtube.readonly", "access_type": "offline", "prompt": "consent", "state": state}
    return "https://accounts.google.com/o/oauth2/v2/auth?" + urllib.parse.urlencode(params)


def finish_youtube_oauth(handler, code, state):
    username = consume_oauth_state(state, "youtube")
    if not username:
        raise ValueError("The YouTube sign-in session expired. Start linking again.")
    config = oauth_config("youtube")
    data = http_form_request("https://oauth2.googleapis.com/token", {"client_id": config["client_id"], "client_secret": config["client_secret"], "code": code, "grant_type": "authorization_code", "redirect_uri": oauth_redirect_uri(handler, "youtube")})
    headers = {"Authorization": "Bearer " + data.get("access_token", "")}
    channels = http_json_request("https://www.googleapis.com/youtube/v3/channels?part=snippet&mine=true", headers)
    channel = (channels.get("items") or [{}])[0]
    snippet = channel.get("snippet") or {}
    channel_id = channel.get("id") or ""
    public = {"linked": True, "channelName": snippet.get("title") or "YouTube", "channelUrl": "https://www.youtube.com/channel/" + channel_id if channel_id else "", "channelId": channel_id, "live": False}
    data["storedAt"] = int(time.time())
    data["expires_at"] = time.time() + int(data.get("expires_in") or 3600)
    save_social_service(username, "youtube", public, data)
    return username


def refresh_google_token(account_key):
    tokens = get_social_tokens(account_key, "youtube")
    if not tokens.get("refresh_token"):
        return tokens
    expires = float(tokens.get("expires_at") or 0)
    if expires > time.time() + 60:
        return tokens
    config = oauth_config("youtube")
    if not config["client_id"] or not config["client_secret"]:
        return tokens
    try:
        data = http_form_request("https://oauth2.googleapis.com/token", {"client_id": config["client_id"], "client_secret": config["client_secret"], "refresh_token": tokens["refresh_token"], "grant_type": "refresh_token"})
    except Exception:
        return tokens
    tokens.update(data)
    tokens["expires_at"] = time.time() + int(data.get("expires_in") or 3600)
    save_social_service(account_key, "youtube", {}, tokens)
    return tokens


def check_social_live(account_key, service):
    cache_key = f"{account_key}:{service}"
    cached = SOCIAL_LIVE_CACHE.get(cache_key)
    if cached and cached.get("expiresAt", 0) > time.time():
        return bool(cached.get("live"))
    live = False
    state = load_socials_state(account_key)
    try:
        if service == "twitch" and state["twitch"].get("linked"):
            config = oauth_config("twitch")
            tokens = get_social_tokens(account_key, "twitch")
            if config["client_id"] and tokens.get("access_token"):
                user = state["twitch"].get("username")
                data = http_json_request("https://api.twitch.tv/helix/streams?user_login=" + urllib.parse.quote(user), {"Authorization": "Bearer " + tokens["access_token"], "Client-Id": config["client_id"]})
                live = bool(data.get("data"))
        elif service == "youtube" and state["youtube"].get("linked"):
            tokens = refresh_google_token(account_key)
            channel_id = state["youtube"].get("channelId")
            if channel_id and tokens.get("access_token"):
                url = "https://www.googleapis.com/youtube/v3/search?part=id&channelId=" + urllib.parse.quote(channel_id) + "&eventType=live&type=video&maxResults=1"
                data = http_json_request(url, {"Authorization": "Bearer " + tokens["access_token"]})
                live = bool(data.get("items"))
    except Exception:
        live = False
    SOCIAL_LIVE_CACHE[cache_key] = {"live": live, "expiresAt": time.time() + SOCIAL_LIVE_CACHE_TTL_SECONDS}
    if service in state and isinstance(state[service], dict) and bool(state[service].get("live")) != live:
        state[service]["live"] = live
        save_socials_state(account_key, state)
    return live


def refresh_public_socials(account_key):
    public = public_socials_state(account_key)
    if public["twitch"]["linked"]:
        public["twitch"]["live"] = check_social_live(account_key, "twitch")
    if public["youtube"]["linked"]:
        public["youtube"]["live"] = check_social_live(account_key, "youtube")
    return public


def save_social_minecraft(account_key, java=None, bedrock=None):
    state = load_socials_state(account_key)
    if java is not None:
        clean = str(java or "").strip()
        if clean and not MINECRAFT_USERNAME_PATTERN.fullmatch(clean):
            raise ValueError("Enter a valid Java Edition Minecraft name (3-16 letters, numbers, or underscores).")
        state["minecraft"]["java"] = clean
    if bedrock is not None:
        clean_bedrock = " ".join(str(bedrock or "").split()).strip()[:40]
        state["minecraft"]["bedrock"] = clean_bedrock
    return save_socials_state(account_key, state)

def ensure_account_storage(paths):
    if read_json_file(paths["watched"], None) is None:
        write_json_file(paths["watched"], [])

    if read_json_file(paths["continue"], None) is None:
        write_json_file(paths["continue"], [])

    if read_json_file(paths["playlists"], None) is None:
        write_json_file(paths["playlists"], [])
    if read_json_file(paths["socials"], None) is None:
        write_json_file(paths["socials"], default_socials_state())


def sanitize_minecraft_username(username):
    clean_username = str(username or "").strip()
    if not MINECRAFT_USERNAME_PATTERN.fullmatch(clean_username):
        raise ValueError("Enter a valid Java Edition Minecraft name (3-16 letters, numbers, or underscores).")

    return clean_username


def load_minecraft_state(account_key):
    paths = get_account_paths(account_key)
    data = read_json_file(paths["minecraft"], {})

    if not isinstance(data, dict):
        data = {}

    username = str(data.get("username") or "").strip()
    if username and not MINECRAFT_USERNAME_PATTERN.fullmatch(username):
        username = ""

    updated_at = int(data.get("updatedAt") or 0)
    return {
        "exists": bool(username),
        "username": username,
        "updatedAt": updated_at,
    }


def save_minecraft_state(account_key, username):
    clean_username = sanitize_minecraft_username(username)
    paths = get_account_paths(account_key)
    write_json_file(
        paths["minecraft"],
        {
            "username": clean_username,
            "updatedAt": int(time.time()),
        },
    )
    return load_minecraft_state(account_key)


def sanitize_optional_media_name(name):
    if not isinstance(name, str) or not name:
        return None

    path = safe_media_path(name)
    if not path or not os.path.exists(path):
        return None

    return name


def sanitize_item_payload(raw_item):
    if not isinstance(raw_item, dict):
        return None

    kind = str(raw_item.get("kind") or "").strip().lower()
    if kind not in {"local", "youtube"}:
        return None

    title = " ".join(str(raw_item.get("title") or "Untitled").split()).strip()[:240] or "Untitled"

    if kind == "local":
        file_name = raw_item.get("file")
        if not isinstance(file_name, str):
            return None

        path = safe_media_path(file_name)
        if not path or not os.path.exists(path):
            return None

        return {
            "kind": "local",
            "file": file_name,
            "title": title,
            "preview": sanitize_optional_media_name(raw_item.get("preview")),
            "logo": sanitize_optional_media_name(raw_item.get("logo")),
            "thumbnail": None,
            "embedUrl": None,
            "videoId": None,
            "sourceLabel": "Local",
            "description": str(raw_item.get("description") or "").strip()[:280] or "Saved local video.",
        }

    video_id = raw_item.get("videoId") or extract_youtube_id(str(raw_item.get("embedUrl") or "").strip())
    if not video_id:
        return None

    return {
        "kind": "youtube",
        "file": None,
        "title": title,
        "preview": None,
        "logo": sanitize_optional_media_name(raw_item.get("logo")),
        "thumbnail": str(raw_item.get("thumbnail") or youtube_thumbnail_url(video_id)).strip(),
        "embedUrl": youtube_embed_url(video_id),
        "videoId": video_id,
        "sourceLabel": str(raw_item.get("sourceLabel") or "YouTube").strip()[:80] or "YouTube",
        "description": (
            str(raw_item.get("description") or "").strip()[:280]
            or "Opens in the embedded YouTube player."
        ),
    }


def build_item_key(item):
    if item["kind"] == "local":
        return f"local::{item['file']}"

    return f"youtube::{item['videoId']}"


def clamp_progress_number(value):
    try:
        number = float(value)
    except (TypeError, ValueError):
        return 0.0

    return max(0.0, number)


def build_progress_record(item, position_seconds, duration_seconds, updated_at=None):
    position = clamp_progress_number(position_seconds)
    duration = clamp_progress_number(duration_seconds)

    if duration and position > duration:
        position = duration

    progress = min(position / duration, 1.0) if duration > 0 else 0.0

    return {
        "id": build_item_key(item),
        "item": item,
        "position": round(position, 2),
        "duration": round(duration, 2),
        "progress": round(progress, 4),
        "updatedAt": int(updated_at or time.time()),
    }


def normalize_progress_records(records):
    normalized = []

    if not isinstance(records, list):
        return normalized

    for entry in records:
        if not isinstance(entry, dict):
            continue

        item = sanitize_item_payload(entry.get("item"))
        if not item:
            continue

        record = build_progress_record(
            item,
            entry.get("position", 0),
            entry.get("duration", 0),
            updated_at=entry.get("updatedAt"),
        )
        normalized.append(record)

    normalized.sort(key=lambda entry: entry.get("updatedAt", 0), reverse=True)
    return normalized


def normalize_playlists(playlists):
    normalized = []

    if not isinstance(playlists, list):
        return normalized

    for entry in playlists:
        if not isinstance(entry, dict):
            continue

        name = sanitize_playlist_name(entry.get("name"))
        if not name:
            continue

        seen = set()
        items = []
        for item in entry.get("items", []):
            clean_item = sanitize_item_payload(item)
            if not clean_item:
                continue

            item_key = build_item_key(clean_item)
            if item_key in seen:
                continue

            seen.add(item_key)
            items.append(clean_item)

        normalized.append(
            {
                "name": name,
                "items": items,
                "updatedAt": int(entry.get("updatedAt") or 0),
            }
        )

    normalized.sort(key=lambda entry: (entry.get("updatedAt", 0), entry["name"].lower()), reverse=True)
    return normalized


def load_account_state(account_key):
    paths = get_account_paths(account_key)
    minecraft_state = load_minecraft_state(account_key)
    socials_state = public_socials_state(account_key)

    if read_json_file(paths["username"], None) is None:
        return {
            "exists": False,
                        "username": "",
            "continueWatching": [],
            "watched": [],
            "playlists": [],
            "minecraft": minecraft_state,
            "socials": socials_state,
            }

    ensure_account_storage(paths)

    username = str(read_json_file(paths["username"], "") or "").strip()
    continue_watching = normalize_progress_records(read_json_file(paths["continue"], []))[:MAX_CONTINUE_ITEMS]
    watched = normalize_progress_records(read_json_file(paths["watched"], []))[:MAX_WATCHED_ITEMS]
    playlists = normalize_playlists(read_json_file(paths["playlists"], []))

    write_json_file(paths["continue"], continue_watching)
    write_json_file(paths["watched"], watched)
    write_json_file(paths["playlists"], playlists)

    return {
        "exists": True,
                "username": username,
        "continueWatching": continue_watching,
        "watched": watched,
        "playlists": playlists,
        "minecraft": minecraft_state,
        "socials": socials_state,
    }


def create_account(account_key, username):
    clean_username = " ".join(str(username or "").split()).strip()[:80]
    if not clean_username:
        raise ValueError("Enter a username first.")

    paths = get_account_paths(account_key)
    ensure_account_storage(paths)

    write_json_file(paths["username"], clean_username)

    return load_account_state(account_key)


def store_playback_progress(account_key, item, position_seconds, duration_seconds, completed=False):
    paths = get_account_paths(account_key)

    if read_json_file(paths["username"], None) is None:
        raise ValueError("Create an account first.")

    ensure_account_storage(paths)

    continue_watching = normalize_progress_records(read_json_file(paths["continue"], []))
    watched = normalize_progress_records(read_json_file(paths["watched"], []))
    record = build_progress_record(item, position_seconds, duration_seconds)

    continue_watching = [entry for entry in continue_watching if entry.get("id") != record["id"]]

    is_complete = bool(completed) or record["progress"] >= WATCHED_PROGRESS_THRESHOLD
    if is_complete:
        watched = [entry for entry in watched if entry.get("id") != record["id"]]
        if record["duration"] > 0:
            record["position"] = record["duration"]
            record["progress"] = 1.0
        watched.insert(0, record)
    elif record["duration"] > 0 and record["position"] >= MIN_PROGRESS_SECONDS:
        continue_watching.insert(0, record)

    write_json_file(paths["continue"], continue_watching[:MAX_CONTINUE_ITEMS])
    write_json_file(paths["watched"], watched[:MAX_WATCHED_ITEMS])


def update_playlist(account_key, playlist_name, item=None):
    paths = get_account_paths(account_key)

    if read_json_file(paths["username"], None) is None:
        raise ValueError("Create an account first.")

    name = sanitize_playlist_name(playlist_name)
    if not name:
        raise ValueError("Enter a playlist name first.")

    ensure_account_storage(paths)
    playlists = normalize_playlists(read_json_file(paths["playlists"], []))
    target = None

    for playlist in playlists:
        if playlist["name"].lower() == name.lower():
            target = playlist
            break

    if target is None:
        target = {"name": name, "items": [], "updatedAt": 0}
        playlists.append(target)

    if item:
        item_key = build_item_key(item)
        target["items"] = [item] + [
            existing for existing in target["items"] if build_item_key(existing) != item_key
        ]

    target["updatedAt"] = int(time.time())
    playlists.sort(key=lambda entry: (entry.get("updatedAt", 0), entry["name"].lower()), reverse=True)
    write_json_file(paths["playlists"], playlists)

    return playlists


def normalize_texture_url(url):
    clean_url = str(url or "").strip()
    if clean_url.startswith("http://"):
        return "https://" + clean_url[len("http://"):]
    return clean_url


def format_uuid(uuid_text):
    compact = str(uuid_text or "").replace("-", "").strip()
    if len(compact) != 32:
        return compact

    return (
        f"{compact[0:8]}-{compact[8:12]}-{compact[12:16]}-"
        f"{compact[16:20]}-{compact[20:32]}"
    )


def build_minecraft_asset_views(username):
    views = [
        ("raw", "Raw Texture", "Original Minecraft skin texture PNG."),
        ("face", "Front Face", "Plain face crop without the hat layer."),
        ("head", "Head", "Head render with the hat and outer layer."),
        ("front", "Front View", "Full-body front render for thumbnails or posters."),
        ("bust", "Bust", "Upper-body render for profile cards and banners."),
        ("back", "Back View", "Full-body back render with back layers."),
    ]

    assets = []
    for view_id, label, description in views:
        preview_query = urllib.parse.urlencode({"username": username, "view": view_id})
        download_query = urllib.parse.urlencode({"username": username, "view": view_id, "download": "1"})
        assets.append(
            {
                "id": view_id,
                "label": label,
                "description": description,
                "previewUrl": f"/minecraft/skin?{preview_query}",
                "downloadUrl": f"/minecraft/skin?{download_query}",
            }
        )

    return assets


def fetch_minecraft_profile(username):
    clean_username = sanitize_minecraft_username(username)
    cache_key = clean_username.lower()
    cached = MINECRAFT_PROFILE_CACHE.get(cache_key)

    if cached and (time.time() - cached["timestamp"]) < MINECRAFT_CACHE_TTL_SECONDS:
        return cached["profile"]

    lookup_url = (
        "https://api.minecraftservices.com/minecraft/profile/lookup/name/"
        + urllib.parse.quote(clean_username)
    )

    try:
        lookup = fetch_remote_json(lookup_url, timeout=MINECRAFT_REQUEST_TIMEOUT)
    except urllib.error.HTTPError as error:
        if error.code == 404:
            raise ValueError(f'Minecraft account "{clean_username}" was not found.') from error
        raise ConnectionError("Minecraft profile lookup is unavailable right now.") from error
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as error:
        raise ConnectionError("Minecraft profile lookup is unavailable right now.") from error

    uuid_text = str(lookup.get("id") or "").replace("-", "").strip()
    profile_name = str(lookup.get("name") or clean_username).strip() or clean_username
    if len(uuid_text) != 32:
        raise ConnectionError("Minecraft profile data came back incomplete.")

    session_url = f"https://sessionserver.mojang.com/session/minecraft/profile/{uuid_text}"
    try:
        session = fetch_remote_json(session_url, timeout=MINECRAFT_REQUEST_TIMEOUT)
    except urllib.error.HTTPError as error:
        if error.code == 204:
            raise ValueError(f'Minecraft skin data for "{profile_name}" is not available right now.') from error
        raise ConnectionError("Minecraft skin data is unavailable right now.") from error
    except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as error:
        raise ConnectionError("Minecraft skin data is unavailable right now.") from error

    textures_payload = {}
    for entry in session.get("properties", []):
        if entry.get("name") != "textures":
            continue

        value = str(entry.get("value") or "")
        if not value:
            continue

        try:
            decoded = base64.b64decode(value)
            textures_payload = json.loads(decoded.decode("utf-8"))
        except (ValueError, json.JSONDecodeError, UnicodeDecodeError):
            textures_payload = {}
        break

    textures = textures_payload.get("textures", {}) if isinstance(textures_payload, dict) else {}
    skin_info = textures.get("SKIN") or {}
    cape_info = textures.get("CAPE") or {}
    skin_url = normalize_texture_url(skin_info.get("url"))

    if not skin_url:
        for skin_entry in (lookup.get("skins") or []):
            if not isinstance(skin_entry, dict):
                continue

            candidate_url = normalize_texture_url(skin_entry.get("url"))
            if candidate_url:
                skin_url = candidate_url
                break

    if not skin_url:
        raise ValueError(f'Minecraft skin data for "{profile_name}" is not available right now.')

    model = "classic"
    if isinstance(skin_info, dict):
        model = "slim" if skin_info.get("metadata", {}).get("model") == "slim" else "classic"

    if model == "classic":
        for skin_entry in (lookup.get("skins") or []):
            if not isinstance(skin_entry, dict):
                continue
            if str(skin_entry.get("variant") or "").strip().upper() == "SLIM":
                model = "slim"
                break

    profile = {
        "username": profile_name,
        "uuid": uuid_text,
        "uuidDashed": format_uuid(uuid_text),
        "model": model,
        "skinUrl": skin_url,
        "capeUrl": normalize_texture_url(cape_info.get("url")),
        "hasCape": bool(cape_info.get("url")),
        "assetViews": build_minecraft_asset_views(profile_name),
    }

    MINECRAFT_PROFILE_CACHE[cache_key] = {
        "timestamp": time.time(),
        "profile": profile,
    }
    return profile


def load_saved_minecraft_profile(account_key):
    state = load_minecraft_state(account_key)
    if not state["exists"]:
        raise ValueError("Save a Minecraft account name first.")

    return fetch_minecraft_profile(state["username"])


def get_minecraft_skin_bytes(profile):
    cache_key = profile["skinUrl"]
    cached = MINECRAFT_TEXTURE_CACHE.get(cache_key)

    if cached and (time.time() - cached["timestamp"]) < MINECRAFT_CACHE_TTL_SECONDS:
        return cached["bytes"]

    try:
        payload = fetch_remote_bytes(profile["skinUrl"], timeout=MINECRAFT_REQUEST_TIMEOUT)
    except (urllib.error.HTTPError, urllib.error.URLError, TimeoutError) as error:
        raise ConnectionError("Minecraft skin download failed. Check the internet connection on this PC.") from error

    MINECRAFT_TEXTURE_CACHE[cache_key] = {
        "timestamp": time.time(),
        "bytes": payload,
    }
    return payload


def get_minecraft_skin_image(profile):
    payload = get_minecraft_skin_bytes(profile)
    try:
        image = Image.open(io.BytesIO(payload))
        return image.convert("RGBA")
    except OSError as error:
        raise ConnectionError("Minecraft skin image could not be decoded.") from error


def crop_skin_region(image, box, fallback_box=None):
    left, top, right, bottom = box
    if right <= image.width and bottom <= image.height:
        return image.crop(box)

    if fallback_box:
        return crop_skin_region(image, fallback_box)

    return None


def paste_skin_region(target, image, source_box, destination, fallback_box=None):
    region = crop_skin_region(image, source_box, fallback_box=fallback_box)
    if region is None:
        return

    target.alpha_composite(region, destination)


def build_front_skin_sprite(image):
    sprite = Image.new("RGBA", (16, 32), (0, 0, 0, 0))

    paste_skin_region(sprite, image, (8, 8, 16, 16), (4, 0))
    paste_skin_region(sprite, image, (20, 20, 28, 32), (4, 8))
    paste_skin_region(sprite, image, (44, 20, 48, 32), (0, 8))
    paste_skin_region(sprite, image, (36, 52, 40, 64), (12, 8), fallback_box=(44, 20, 48, 32))
    paste_skin_region(sprite, image, (4, 20, 8, 32), (4, 20))
    paste_skin_region(sprite, image, (20, 52, 24, 64), (8, 20), fallback_box=(4, 20, 8, 32))

    paste_skin_region(sprite, image, (40, 8, 48, 16), (4, 0))
    paste_skin_region(sprite, image, (20, 36, 28, 48), (4, 8))
    paste_skin_region(sprite, image, (44, 36, 48, 48), (0, 8))
    paste_skin_region(sprite, image, (52, 52, 56, 64), (12, 8))
    paste_skin_region(sprite, image, (4, 36, 8, 48), (4, 20))
    paste_skin_region(sprite, image, (4, 52, 8, 64), (8, 20))

    return sprite


def build_back_skin_sprite(image):
    sprite = Image.new("RGBA", (16, 32), (0, 0, 0, 0))

    paste_skin_region(sprite, image, (24, 8, 32, 16), (4, 0))
    paste_skin_region(sprite, image, (32, 20, 40, 32), (4, 8))
    paste_skin_region(sprite, image, (52, 20, 56, 32), (0, 8))
    paste_skin_region(sprite, image, (44, 52, 48, 64), (12, 8), fallback_box=(52, 20, 56, 32))
    paste_skin_region(sprite, image, (12, 20, 16, 32), (4, 20))
    paste_skin_region(sprite, image, (28, 52, 32, 64), (8, 20), fallback_box=(12, 20, 16, 32))

    paste_skin_region(sprite, image, (56, 8, 64, 16), (4, 0))
    paste_skin_region(sprite, image, (32, 36, 40, 48), (4, 8))
    paste_skin_region(sprite, image, (52, 36, 56, 48), (0, 8))
    paste_skin_region(sprite, image, (60, 52, 64, 64), (12, 8))
    paste_skin_region(sprite, image, (12, 36, 16, 48), (4, 20))
    paste_skin_region(sprite, image, (12, 52, 16, 64), (8, 20))

    return sprite


def image_to_png_bytes(image):
    buffer = io.BytesIO()
    image.save(buffer, format="PNG")
    return buffer.getvalue()


def render_minecraft_skin_view(profile, view_name):
    normalized_view = str(view_name or "head").strip().lower()
    file_name = f"{profile['username']}-{normalized_view}.png"

    if normalized_view == "raw":
        return get_minecraft_skin_bytes(profile), file_name

    image = get_minecraft_skin_image(profile)

    if normalized_view == "face":
        face = crop_skin_region(image, (8, 8, 16, 16))
        if face is None:
            raise ValueError("The Minecraft face texture could not be generated.")
        return image_to_png_bytes(face.resize((256, 256), Image.NEAREST)), file_name

    if normalized_view == "head":
        head = Image.new("RGBA", (8, 8), (0, 0, 0, 0))
        paste_skin_region(head, image, (8, 8, 16, 16), (0, 0))
        paste_skin_region(head, image, (40, 8, 48, 16), (0, 0))
        return image_to_png_bytes(head.resize((256, 256), Image.NEAREST)), file_name

    if normalized_view == "front":
        front = build_front_skin_sprite(image)
        return image_to_png_bytes(front.resize((256, 512), Image.NEAREST)), file_name

    if normalized_view == "back":
        back = build_back_skin_sprite(image)
        return image_to_png_bytes(back.resize((256, 512), Image.NEAREST)), file_name

    if normalized_view == "bust":
        front = build_front_skin_sprite(image)
        bust = front.crop((0, 0, 16, 20))
        return image_to_png_bytes(bust.resize((256, 320), Image.NEAREST)), file_name

    raise ValueError("Unsupported Minecraft skin view.")



class Handler(BaseHTTPRequestHandler):

    def log_message(self, format, *args):
        # URLs can contain private search terms or tokens; do not log them.
        return

    def end_headers(self):
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Referrer-Policy", "strict-origin-when-cross-origin")
        self.send_header("Permissions-Policy", "camera=(), microphone=(), geolocation=(), payment=()")
        self.send_header("Cross-Origin-Opener-Policy", "same-origin")
        self.send_header("Cross-Origin-Resource-Policy", "same-origin")
        nonce = getattr(self, "_csp_nonce", "")
        if nonce:
            self.send_header(
                "Content-Security-Policy",
                "default-src 'self'; base-uri 'none'; object-src 'none'; "
                "form-action 'self'; frame-ancestors 'none'; "
                "script-src 'nonce-" + nonce + "' 'strict-dynamic' https://www.youtube.com; "
                "style-src 'self' 'nonce-" + nonce + "'; "
                "img-src 'self' data: blob: https://images.unsplash.com https://i.ytimg.com; "
                "media-src 'self' blob:; connect-src 'self'; "
                "frame-src https://www.youtube-nocookie.com",
            )
        super().end_headers()

    def client_ip(self):
        return self.client_address[0]

    def is_allowed_origin(self):
        origin = self.headers.get("Origin", "").rstrip("/").lower()
        if not origin:
            return False
        hosts = {"localhost", "127.0.0.1", "[::1]", get_local_ip().lower()}
        hosts.update(name.lower() for name in certificate_dns_names())
        allowed = {f"https://{host}:{PORT}" for host in hosts}
        allowed.update(
            value.strip().rstrip("/").lower()
            for value in os.environ.get("NOTFLIX_ALLOWED_ORIGINS", "").split(",")
            if value.strip().lower().startswith("https://")
        )
        return hmac.compare_digest(origin, next((item for item in allowed if item == origin), ""))

    def allow_request(self, bucket, maximum, window_seconds):
        now = time.monotonic()
        key = (bucket, self.client_ip())
        with RATE_LIMIT_LOCK:
            requests = RATE_LIMITS.get(key, [])
            requests = [stamp for stamp in requests if now - stamp < window_seconds]
            if len(requests) >= maximum:
                RATE_LIMITS[key] = requests
                return False
            requests.append(now)
            RATE_LIMITS[key] = requests
            if len(RATE_LIMITS) > 4096:
                expired_before = now - max(AUTH_RATE_WINDOW_SECONDS, WRITE_RATE_WINDOW_SECONDS)
                for old_key, timestamps in list(RATE_LIMITS.items()):
                    if not timestamps or timestamps[-1] < expired_before:
                        RATE_LIMITS.pop(old_key, None)
        return True

    def validate_csrf(self):
        expected = get_session_csrf_token(self.get_session_token())
        provided = self.headers.get("X-CSRF-Token", "")
        return bool(expected and provided and hmac.compare_digest(expected, provided))

    def safe_write(self, data):
        try:
            self.wfile.write(data)
        except (BrokenPipeError, ConnectionAbortedError):
            pass

    def send_json(self, payload, status=200, session_token="", clear_session=False):
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Pragma", "no-cache")
        if session_token:
            self.send_header("Set-Cookie", f"{SESSION_COOKIE_NAME}={session_token}; Path=/; HttpOnly; Secure; SameSite=Strict; Max-Age={SESSION_TTL_SECONDS}")
        elif clear_session:
            self.send_header("Set-Cookie", f"{SESSION_COOKIE_NAME}=; Path=/; HttpOnly; Secure; SameSite=Strict; Max-Age=0")
        self.end_headers()
        self.safe_write(json.dumps(payload, ensure_ascii=False).encode("utf-8"))

    def get_session_token(self):
        try:
            cookie = SimpleCookie()
            cookie.load(self.headers.get("Cookie", ""))
            morsel = cookie.get(SESSION_COOKIE_NAME)
            return morsel.value if morsel else ""
        except (TypeError, ValueError):
            return ""

    def get_current_username(self):
        return get_session_username(self.get_session_token())

    def require_user(self):
        username = self.get_current_username()
        if not username or not find_user(username):
            self.send_json({"error": "Sign in to use this feature."}, status=401)
            return ""
        return username

    def read_json_body(self):
        try:
            length = int(self.headers.get("Content-Length", "0") or "0")
        except ValueError as error:
            raise ValueError("Invalid JSON size.") from error
        if length < 0 or length > MAX_JSON_BODY_BYTES:
            raise ValueError(
                f"JSON requests are limited to {MAX_JSON_BODY_BYTES // (1024 * 1024)} MB."
            )
        raw_body = self.rfile.read(length) if length > 0 else b""

        if not raw_body:
            return {}

        try:
            return json.loads(raw_body.decode("utf-8"))
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise ValueError("Invalid JSON body.") from error

    def read_upload_form(self):
        try:
            length = int(self.headers.get("Content-Length", "0") or "0")
        except ValueError as error:
            raise ValueError("Invalid upload size.") from error

        if length <= 0:
            raise ValueError("Choose at least one file to publish.")
        if length > MAX_UPLOAD_TOTAL_BYTES:
            raise ValueError(f"Uploads are limited to {MAX_UPLOAD_TOTAL_BYTES // (1024 * 1024)} MB at a time.")

        return parse_multipart_form(self.headers.get("Content-Type", ""), self.rfile.read(length))

    def do_GET(self):
        if self.path == "/":
            self.send_home()
        elif self.path in {"/account", "/auth/me"}:
            self.send_account()
        elif self.path == "/users":
            self.send_users()
        elif self.path.startswith("/profile/picture/"):
            self.send_profile_picture()
        elif self.path.startswith("/profile"):
            self.send_social_profile()
        elif self.path == "/socials/status":
            self.send_social_status()
        elif self.path.startswith("/socials/twitch/callback"):
            self.social_oauth_callback("twitch")
        elif self.path.startswith("/socials/youtube/callback"):
            self.social_oauth_callback("youtube")
        elif self.path == "/chat/global":
            self.send_global_chat()
        elif self.path.startswith("/chat/direct"):
            self.send_direct_chat()
        elif self.path == "/list":
            self.send_list()
        elif self.path == "/uploads":
            self.send_uploads()
        elif self.path == "/drawings":
            self.send_drawings()
        elif self.path.startswith("/drawings/image/"):
            self.send_drawing_image()
        elif self.path == "/feedback":
            self.send_feedback()
        elif self.path.startswith("/uploads/download"):
            self.send_upload_download()
        elif self.path.startswith("/minecraft/profile"):
            self.send_minecraft_profile()
        elif self.path.startswith("/minecraft/skin"):
            self.send_minecraft_skin()
        elif self.path.startswith("/youtube/random"):
            self.send_youtube_random()
        elif self.path.startswith("/youtube/search"):
            self.send_youtube_search()
        elif self.path.startswith("/movie/"):
            self.stream_file()
        elif self.path.startswith("/preview/"):
            self.stream_file(preview=True)
        elif self.path.startswith("/logo/"):
            self.serve_logo()
        else:
            self.send_error(404)

    def do_POST(self):
        public_auth_routes = {"/auth/register", "/auth/login"}
        if not self.is_allowed_origin():
            self.send_json({"error": "Requests must come from this HTTPS site."}, status=403)
            return
        if self.path in public_auth_routes:
            if not self.allow_request("auth", AUTH_RATE_LIMIT, AUTH_RATE_WINDOW_SECONDS):
                self.send_json({"error": "Too many sign-in attempts. Please wait and try again."}, status=429)
                return
        else:
            if not self.validate_csrf():
                self.send_json({"error": "Your session check failed. Refresh the page and try again."}, status=403)
                return
            if not self.allow_request("write", WRITE_RATE_LIMIT, WRITE_RATE_WINDOW_SECONDS):
                self.send_json({"error": "Too many requests. Please wait a moment and try again."}, status=429)
                return

        if self.path == "/auth/register":
            self.register_account()
        elif self.path == "/auth/login":
            self.login_account()
        elif self.path == "/auth/logout":
            self.logout_account()
        elif self.path == "/profile/picture":
            self.save_profile_picture()
        elif self.path == "/socials/microsoft":
            self.save_manual_microsoft_link()
        elif self.path == "/socials/microsoft/start":
            self.start_microsoft_link()
        elif self.path == "/socials/microsoft/poll":
            self.poll_microsoft_link()
        elif self.path == "/socials/twitch/start":
            self.start_social_oauth("twitch")
        elif self.path == "/socials/youtube/start":
            self.start_social_oauth("youtube")
        elif self.path == "/socials/minecraft":
            self.save_social_minecraft()
        elif self.path == "/chat/global":
            self.create_global_chat()
        elif self.path == "/chat/direct":
            self.create_direct_chat()
        elif self.path == "/account/progress":
            self.save_account_progress()
        elif self.path == "/account/playlists":
            self.save_playlist()
        elif self.path == "/minecraft/profile":
            self.save_minecraft_profile()
        elif self.path == "/uploads":
            self.create_uploads()
        elif self.path == "/drawings":
            self.create_drawing()
        elif self.path == "/feedback":
            self.create_feedback()
        elif self.path == "/feedback/update":
            self.update_feedback()
        else:
            self.send_error(404)

    def account_state_payload(self, username):
        state = load_account_state(username)
        profile = public_user(find_user(username)) if username else None
        state["profilePictureUrl"] = profile.get("profilePictureUrl", "") if profile else ""
        state["csrfToken"] = get_session_csrf_token(self.get_session_token()) if username else ""
        return state

    def send_account(self):
        self.send_json(self.account_state_payload(self.get_current_username()))

    def register_account(self):
        try:
            payload = self.read_json_body()
            user = register_user(payload.get("username"), payload.get("password"))
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        token = create_session(user["username"])
        self.send_json(self.account_state_payload(user["username"]), status=201, session_token=token)

    def login_account(self):
        try:
            payload = self.read_json_body()
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        user = find_user(payload.get("username"))
        if not user or not verify_password(payload.get("password"), user.get("passwordHash")):
            self.send_json({"error": "Incorrect username or password."}, status=401)
            return
        token = create_session(user["username"])
        self.send_json(self.account_state_payload(user["username"]), session_token=token)

    def logout_account(self):
        remove_session(self.get_session_token())
        self.send_json(self.account_state_payload(""), clear_session=True)

    def send_social_status(self):
        username = self.require_user()
        if username:
            self.send_json({"socials": refresh_public_socials(username)})

    def send_social_profile(self):
        username = self.require_user()
        if not username:
            return
        parsed = urllib.parse.urlparse(self.path)
        target = urllib.parse.parse_qs(parsed.query).get("user", [""])[0].strip()
        user = find_user(target)
        if not user:
            self.send_json({"error": "That user does not exist."}, status=404)
            return
        profile = public_user(user)
        profile["socials"] = refresh_public_socials(user["username"])
        self.send_json({"profile": profile})

    def save_manual_microsoft_link(self):
        username = self.require_user()
        if not username:
            return
        try:
            payload = self.read_json_body()
            socials = save_manual_microsoft_link(username, payload.get("displayName"), payload.get("email"), payload.get("accountId"))
            self.send_json({"ok": True, "socials": socials})
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)

    def start_microsoft_link(self):
        username = self.require_user()
        if not username:
            return
        try:
            self.send_json(microsoft_device_start(username))
        except (ValueError, urllib.error.URLError, TimeoutError) as error:
            self.send_json({"error": str(error)}, status=400)

    def poll_microsoft_link(self):
        username = self.require_user()
        if not username:
            return
        try:
            self.send_json(microsoft_device_poll(username))
        except (ValueError, urllib.error.URLError, TimeoutError) as error:
            self.send_json({"error": str(error)}, status=400)

    def start_social_oauth(self, provider):
        username = self.require_user()
        if not username:
            return
        try:
            url = build_twitch_auth_url(self, username) if provider == "twitch" else build_youtube_auth_url(self, username)
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        self.send_json({"url": url})

    def social_oauth_callback(self, provider):
        parsed = urllib.parse.urlparse(self.path)
        params = urllib.parse.parse_qs(parsed.query)
        error = params.get("error", [""])[0]
        if error:
            self.send_response(302)
            self.send_header("Location", "/#social-error=" + urllib.parse.quote(error))
            self.end_headers()
            return
        try:
            if provider == "twitch":
                username = finish_twitch_oauth(self, params.get("code", [""])[0], params.get("state", [""])[0])
            else:
                username = finish_youtube_oauth(self, params.get("code", [""])[0], params.get("state", [""])[0])
            self.send_response(302)
            self.send_header("Location", "/#social-linked=" + provider)
            self.end_headers()
        except (ValueError, urllib.error.URLError, TimeoutError) as exc:
            self.send_response(302)
            self.send_header("Location", "/#social-error=" + urllib.parse.quote(str(exc)))
            self.end_headers()

    def save_social_minecraft(self):
        username = self.require_user()
        if not username:
            return
        try:
            payload = self.read_json_body()
            socials = save_social_minecraft(username, payload.get("java"), payload.get("bedrock"))
            self.send_json({"ok": True, "socials": socials})
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)

    def send_users(self):
        username = self.require_user()
        if username:
            self.send_json({"items": list_public_users(username)})

    def send_global_chat(self):
        username = self.require_user()
        if username:
            self.send_json({"items": list_global_messages()})

    def create_global_chat(self):
        username = self.require_user()
        if not username:
            return
        try:
            message = send_global_message(username, self.read_json_body().get("text"))
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        self.send_json({"ok": True, "item": message}, status=201)

    def send_direct_chat(self):
        username = self.require_user()
        if not username:
            return
        other = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query).get("with", [""])[0]
        try:
            self.send_json({"items": list_direct_messages(username, other)})
        except ValueError as error:
            self.send_json({"error": str(error)}, status=404)

    def create_direct_chat(self):
        username = self.require_user()
        if not username:
            return
        try:
            payload = self.read_json_body()
            message = send_direct_message(username, payload.get("recipient"), payload.get("text"))
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        self.send_json({"ok": True, "item": message}, status=201)

    def save_profile_picture(self):
        username = self.require_user()
        if not username:
            return
        try:
            fields, files = self.read_upload_form()
            if len(files) != 1:
                raise ValueError("Choose exactly one profile picture.")
            profile = update_profile_picture(username, files[0])
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        except OSError:
            self.send_json({"error": "The profile picture could not be saved."}, status=500)
            return
        self.send_json({"ok": True, "profile": profile})

    def send_profile_picture(self):
        name = urllib.parse.unquote(self.path.replace("/profile/picture/", ""))
        path = safe_profile_picture_path(name)
        blob = _blob_get(path) if path else None
        if not blob:
            self.send_error(404)
            return
        self.send_response(200)
        self.send_header("Content-Type", blob["content_type"])
        self.send_header("Content-Length", str(blob["size"]))
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.safe_write(blob["data"])

    def save_account_progress(self):
        try:
            payload = self.read_json_body()
            item = sanitize_item_payload(payload.get("item"))
            if not item:
                raise ValueError("Invalid media item.")

            username = self.require_user()
            if not username:
                return
            store_playback_progress(
                username,
                item,
                payload.get("position", 0),
                payload.get("duration", 0),
                completed=payload.get("completed", False),
            )
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return

        self.send_json({"ok": True})

    def save_playlist(self):
        try:
            payload = self.read_json_body()
            item = payload.get("item")
            clean_item = sanitize_item_payload(item) if item else None
            username = self.require_user()
            if not username:
                return
            playlists = update_playlist(username, payload.get("name"), item=clean_item)
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return

        self.send_json({"ok": True, "playlists": playlists})

    def send_minecraft_profile(self):
        username = self.require_user()
        if not username:
            return
        parsed = urllib.parse.urlparse(self.path)
        requested_username = urllib.parse.parse_qs(parsed.query).get("username", [""])[0].strip()

        try:
            if requested_username:
                profile = fetch_minecraft_profile(requested_username)
            else:
                profile = load_saved_minecraft_profile(username)
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        except ConnectionError as error:
            self.send_json({"error": str(error)}, status=502)
            return

        self.send_json(
            {
                "minecraft": load_minecraft_state(username),
                "profile": profile,
            }
        )

    def save_minecraft_profile(self):
        username = self.require_user()
        if not username:
            return
        try:
            payload = self.read_json_body()
            profile = fetch_minecraft_profile(payload.get("username"))
            minecraft_state = save_minecraft_state(username, profile["username"])
            save_social_minecraft(username, java=profile["username"])
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        except ConnectionError as error:
            self.send_json({"error": str(error)}, status=502)
            return

        self.send_json(
            {
                "ok": True,
                "minecraft": minecraft_state,
                "profile": profile,
            },
            status=201,
        )

    def send_minecraft_skin(self):
        username = self.require_user()
        if not username:
            return
        parsed = urllib.parse.urlparse(self.path)
        params = urllib.parse.parse_qs(parsed.query)
        requested_username = params.get("username", [""])[0].strip()
        requested_view = params.get("view", ["head"])[0].strip()
        wants_download = params.get("download", ["0"])[0].strip() == "1"

        try:
            if requested_username:
                profile = fetch_minecraft_profile(requested_username)
            else:
                profile = load_saved_minecraft_profile(username)

            payload, file_name = render_minecraft_skin_view(profile, requested_view)
        except ValueError:
            self.send_error(400)
            return
        except ConnectionError:
            self.send_error(502)
            return

        self.send_response(200)
        self.send_header("Content-Type", mimetypes.guess_type(path)[0] or "application/octet-stream")
        self.send_header("Cache-Control", "public, max-age=300")
        if wants_download:
            self.send_header("Content-Disposition", f'attachment; filename="{file_name}"')
        self.end_headers()
        self.safe_write(payload)

    def send_list(self):
        self.send_json(get_movies())

    def send_uploads(self):
        self.send_json({"items": [public_upload_record(record) for record in read_upload_catalog()]})

    def create_uploads(self):
        account = load_account_state(self.get_current_username())
        if not account.get("exists"):
            self.send_json({"error": "Sign in before publishing an upload."}, status=403)
            return

        try:
            fields, files = self.read_upload_form()
            created = publish_uploads(files, fields, account.get("username") or "NotFlix creator")
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        except OSError:
            self.send_json({"error": "The upload could not be saved."}, status=500)
            return

        self.send_json({"ok": True, "items": created}, status=201)

    def send_drawings(self):
        self.send_json({"items": list_drawings()})

    def send_drawing_image(self):
        parsed = urllib.parse.urlparse(self.path)
        name = parsed.path.split("/drawings/image/", 1)[-1]
        path = safe_drawing_path(urllib.parse.unquote(name))
        blob = _blob_get(path) if path else None
        if not blob:
            self.send_error(404)
            return
        self.send_response(200)
        self.send_header("Content-Type", blob["content_type"])
        self.send_header("Cache-Control", "public, max-age=3600")
        self.send_header("Content-Length", str(blob["size"]))
        self.end_headers()
        self.safe_write(blob["data"])

    def send_feedback(self):
        username = self.get_current_username()
        items = list_feedback()
        # Everyone can submit and read the public board; management controls are only for Raphuz.
        self.send_json({"items": items, "admin": is_feedback_admin(username)})

    def create_drawing(self):
        username = self.get_current_username()
        if not username or not load_account_state(username).get("exists"):
            self.send_json({"error": "Sign in before sharing a drawing."}, status=403)
            return
        try:
            payload = self.read_json_body()
            drawing = save_drawing(username, payload.get("title"), payload.get("image"))
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        except OSError:
            self.send_json({"error": "The drawing could not be saved."}, status=500)
            return
        self.send_json({"ok": True, "drawing": drawing}, status=201)

    def create_feedback(self):
        username = self.get_current_username()
        if not username or not load_account_state(username).get("exists"):
            self.send_json({"error": "Sign in before sending feedback."}, status=403)
            return
        try:
            payload = self.read_json_body()
            item = submit_feedback(username, payload.get("message"))
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        self.send_json({"ok": True, "item": item}, status=201)

    def update_feedback(self):
        username = self.get_current_username()
        if not is_feedback_admin(username):
            self.send_json({"error": "Only the Raphuz account can manage the feedback board."}, status=403)
            return
        try:
            payload = self.read_json_body()
            item = update_feedback_admin(username, payload.get("id"), payload.get("bucketlisted"), payload.get("fixed"), payload.get("status"))
        except PermissionError as error:
            self.send_json({"error": str(error)}, status=403)
            return
        except ValueError as error:
            self.send_json({"error": str(error)}, status=400)
            return
        self.send_json({"ok": True, "item": item})

    def send_upload_download(self):
        parsed = urllib.parse.urlparse(self.path)
        upload_id = urllib.parse.parse_qs(parsed.query).get("id", [""])[0].lower()
        record = next((item for item in read_upload_catalog() if item["id"] == upload_id), None)
        if not record:
            self.send_error(404)
            return

        path = safe_upload_path(record["storageName"])
        blob = _blob_get(path) if path else None
        if not blob:
            self.send_error(404)
            return

        safe_name = re.sub(r"[^A-Za-z0-9._ -]+", "_", record["originalName"]).strip() or "notflix-download"
        self.send_response(200)
        self.send_header("Content-Type", blob["content_type"])
        self.send_header("Content-Length", str(blob["size"]))
        self.send_header("Content-Disposition", f'attachment; filename="{safe_name}"')
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.safe_write(blob["data"])

    def send_youtube_random(self):
        try:
            query, items = get_random_youtube_results()
        except Exception:
            self.send_json(
                {
                    "query": "",
                    "items": [],
                    "error": "Random YouTube videos are unavailable right now. Check the internet connection on this PC.",
                },
                status=502,
            )
            return

        self.send_json({"query": query, "items": items})

    def send_youtube_search(self):
        parsed = urllib.parse.urlparse(self.path)
        query = urllib.parse.parse_qs(parsed.query).get("q", [""])[0].strip()

        if not query:
            self.send_json({"query": "", "items": [], "error": "Enter a YouTube search term first."}, status=400)
            return

        try:
            items = fetch_youtube_search_results(query)
        except (urllib.error.URLError, TimeoutError, ValueError, json.JSONDecodeError):
            self.send_json(
                {
                    "query": query,
                    "items": [],
                    "error": "YouTube search is unavailable right now. Check the internet connection on this PC.",
                },
                status=502,
            )
            return

        self.send_json({"query": query, "items": items})

    def send_home(self):
        self._csp_nonce = secrets.token_urlsafe(24)
        html = """<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0" />
  <title>NotFlix</title>
  <style>
    :root {
      color-scheme: dark;
      --bg: #070707;
      --panel: rgba(16, 16, 16, 0.88);
      --panel-soft: rgba(255, 255, 255, 0.05);
      --text: #f7f7f7;
      --muted: #b8b8b8;
      --accent: #e50914;
      --accent-soft: rgba(229, 9, 20, 0.18);
      --accent-bright: #ff3b45;
      --electric: #8b5cf6;
      --border: rgba(255, 255, 255, 0.12);
      --shadow: rgba(0, 0, 0, 0.38);
    }

    * {
      box-sizing: border-box;
      margin: 0;
      padding: 0;
    }

    html {
      scroll-behavior: smooth;
    }

    body {
      min-height: 100vh;
      font-family: Arial, Helvetica, sans-serif;
      color: var(--text);
      background:
        radial-gradient(circle at 14% 0%, rgba(229, 9, 20, 0.28), transparent 26%),
        radial-gradient(circle at 86% 18%, rgba(119, 82, 235, 0.16), transparent 24%),
        linear-gradient(180deg, #171717 0%, #080808 45%, #050505 100%);
      overflow-x: hidden;
    }

    button,
    input,
    textarea {
      font: inherit;
    }

    button {
      border: 0;
      border-radius: 999px;
      padding: 12px 18px;
      font-weight: 700;
      cursor: pointer;
      transition: transform 0.18s ease, opacity 0.18s ease, background 0.18s ease, box-shadow 0.18s ease;
    }

    button:hover {
      transform: translateY(-1px);
    }

    button:disabled {
      opacity: 0.55;
      cursor: not-allowed;
      transform: none;
    }

    button.primary {
      background: linear-gradient(135deg, var(--accent-bright), var(--accent));
      color: white;
      box-shadow: 0 12px 26px rgba(229, 9, 20, 0.22);
    }

    button.primary:hover {
      box-shadow: 0 16px 34px rgba(229, 9, 20, 0.34);
    }

    button.secondary {
      background: rgba(255, 255, 255, 0.08);
      color: var(--text);
      border: 1px solid var(--border);
    }

    button.ghost {
      background: transparent;
      color: var(--text);
      border: 1px solid rgba(255, 255, 255, 0.18);
    }

    button.card-chip,
    button.pill {
      padding: 8px 12px;
      font-size: 0.88rem;
    }

    button.pill.active {
      background: var(--accent);
      color: white;
    }

    header {
      position: sticky;
      top: 0;
      z-index: 60;
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 16px;
      padding: 18px 24px;
      background: linear-gradient(to bottom, rgba(4, 4, 5, 0.94), rgba(4, 4, 5, 0.64));
      backdrop-filter: blur(14px);
      border-bottom: 1px solid rgba(255, 255, 255, 0.08);
    }

    .brand {
      color: var(--accent);
      font-size: 1.8rem;
      font-weight: 900;
      letter-spacing: 0.08em;
    }

    .header-actions,
    .hero-actions,
    .hero-meta,
    .toolbar,
    .pill-row,
    .account-pills {
      display: flex;
      flex-wrap: wrap;
      gap: 12px;
    }

    .header-actions {
      justify-content: flex-end;
    }

    main {
      padding: 28px 24px 44px;
    }

    .hero {
      position: relative;
      overflow: hidden;
      border-radius: 28px;
      min-height: 360px;
      padding: 36px;
      display: flex;
      align-items: flex-end;
      background:
        linear-gradient(120deg, rgba(0, 0, 0, 0.9), rgba(0, 0, 0, 0.36)),
        url("https://images.unsplash.com/photo-1489599849927-2ee91cede3ba?q=80&w=1800&auto=format&fit=crop") center/cover no-repeat;
      border: 1px solid rgba(255, 255, 255, 0.08);
      box-shadow: 0 28px 70px rgba(0, 0, 0, 0.34);
    }

    .hero::before {
      content: "";
      position: absolute;
      width: 410px;
      height: 410px;
      right: -120px;
      top: -210px;
      border-radius: 50%;
      background: radial-gradient(circle, rgba(229, 9, 20, 0.68), transparent 68%);
      filter: blur(4px);
    }

    .hero-content {
      max-width: 760px;
      position: relative;
      z-index: 1;
    }

    .eyebrow {
      display: inline-flex;
      margin-bottom: 16px;
      padding: 8px 12px;
      border-radius: 999px;
      background: var(--accent-soft);
      color: #ffd7d9;
      font-size: 0.92rem;
    }

    .hero h1 {
      font-size: clamp(2.4rem, 6vw, 4.7rem);
      line-height: 0.95;
      margin-bottom: 18px;
    }

    .hero p {
      max-width: 640px;
      color: #dcdcdc;
      font-size: 1.05rem;
      line-height: 1.62;
      margin-bottom: 26px;
    }

    .hero-meta span,
    .account-pill {
      padding: 9px 12px;
      border-radius: 999px;
      background: rgba(255, 255, 255, 0.08);
      border: 1px solid rgba(255, 255, 255, 0.08);
      color: #f0f0f0;
    }

    .spotlight {
      position: relative;
      isolation: isolate;
      display: grid;
      grid-template-columns: minmax(0, 1.18fr) minmax(240px, 0.82fr);
      gap: 28px;
      align-items: stretch;
      overflow: hidden;
      margin-top: 26px;
      min-height: 270px;
      padding: 28px;
      border: 1px solid rgba(255, 255, 255, 0.11);
      border-radius: 28px;
      background:
        radial-gradient(circle at 100% 0%, rgba(139, 92, 246, 0.24), transparent 34%),
        linear-gradient(120deg, rgba(255, 255, 255, 0.08), rgba(255, 255, 255, 0.025)),
        #101010;
      box-shadow: 0 24px 55px var(--shadow);
    }

    .spotlight-copy {
      display: flex;
      flex-direction: column;
      align-items: flex-start;
      justify-content: center;
      min-width: 0;
    }

    .spotlight-label {
      display: inline-flex;
      align-items: center;
      gap: 8px;
      margin-bottom: 14px;
      color: #f8c9cb;
      font-size: 0.78rem;
      font-weight: 800;
      letter-spacing: 0.14em;
      text-transform: uppercase;
    }

    .spotlight-label::before {
      content: "";
      width: 8px;
      height: 8px;
      border-radius: 50%;
      background: var(--accent-bright);
      box-shadow: 0 0 16px var(--accent-bright);
    }

    .spotlight h2 {
      max-width: 620px;
      font-size: clamp(1.95rem, 4vw, 3.2rem);
      line-height: 1.04;
      letter-spacing: -0.04em;
    }

    .spotlight p {
      max-width: 620px;
      margin-top: 12px;
      color: var(--muted);
      line-height: 1.6;
    }

    .spotlight-actions {
      display: flex;
      flex-wrap: wrap;
      gap: 10px;
      margin-top: 22px;
    }

    .spotlight-art {
      position: relative;
      display: grid;
      min-height: 212px;
      overflow: hidden;
      place-items: end start;
      padding: 20px;
      border-radius: 22px;
      background:
        radial-gradient(circle at 22% 20%, rgba(255, 255, 255, 0.15), transparent 22%),
        linear-gradient(135deg, #362020, #17132c 60%, #0c0c0f);
      border: 1px solid rgba(255, 255, 255, 0.1);
    }

    .spotlight-art::after {
      content: "";
      position: absolute;
      inset: 0;
      z-index: 1;
      background: linear-gradient(0deg, rgba(0, 0, 0, 0.76), transparent 66%);
      pointer-events: none;
    }

    .spotlight-art img {
      position: absolute;
      inset: 0;
      width: 100%;
      height: 100%;
      object-fit: cover;
      opacity: 0.86;
    }

    .spotlight-type {
      position: relative;
      z-index: 2;
      padding: 8px 11px;
      border: 1px solid rgba(255, 255, 255, 0.16);
      border-radius: 999px;
      background: rgba(7, 7, 7, 0.6);
      font-size: 0.8rem;
      font-weight: 800;
      letter-spacing: 0.08em;
      text-transform: uppercase;
    }

    .launch-panel {
      background:
        radial-gradient(circle at 4% 0%, rgba(229, 9, 20, 0.16), transparent 28%),
        linear-gradient(180deg, rgba(255, 255, 255, 0.045), rgba(255, 255, 255, 0.012)),
        var(--panel);
    }

    .launch-grid {
      display: grid;
      grid-template-columns: repeat(4, minmax(0, 1fr));
      gap: 14px;
    }

    .launch-card {
      min-height: 190px;
      padding: 20px;
      border: 1px solid rgba(255, 255, 255, 0.09);
      border-radius: 22px;
      background: rgba(255, 255, 255, 0.04);
      transition: transform 0.18s ease, border-color 0.18s ease, background 0.18s ease;
    }

    .launch-card:hover {
      transform: translateY(-4px);
      border-color: rgba(255, 255, 255, 0.22);
      background: rgba(255, 255, 255, 0.07);
    }

    .launch-icon {
      display: grid;
      width: 42px;
      height: 42px;
      margin-bottom: 20px;
      place-items: center;
      border-radius: 14px;
      background: linear-gradient(135deg, rgba(229, 9, 20, 0.9), rgba(139, 92, 246, 0.8));
      box-shadow: 0 10px 22px rgba(0, 0, 0, 0.24);
      font-size: 1.1rem;
    }

    .launch-card h3 {
      font-size: 1.08rem;
    }

    .launch-card p {
      margin-top: 7px;
      color: var(--muted);
      font-size: 0.93rem;
      line-height: 1.48;
    }

    .launch-card button {
      margin-top: 16px;
      padding: 9px 13px;
      font-size: 0.86rem;
    }

    .panel {
      margin-top: 26px;
      padding: 24px;
      border-radius: 28px;
      background:
        linear-gradient(180deg, rgba(255, 255, 255, 0.03), rgba(255, 255, 255, 0.01)),
        var(--panel);
      border: 1px solid rgba(255, 255, 255, 0.08);
      box-shadow: 0 24px 55px rgba(0, 0, 0, 0.2);
    }

    .section-head {
      display: flex;
      align-items: flex-start;
      justify-content: space-between;
      gap: 16px;
      margin-bottom: 18px;
    }

    .section-copy h2 {
      font-size: 1.8rem;
      margin-bottom: 8px;
    }

    .section-copy p {
      color: var(--muted);
      line-height: 1.55;
    }

    .tool-row {
      display: flex;
      flex-wrap: wrap;
      gap: 12px;
      margin-bottom: 18px;
    }

    .search-wrap {
      flex: 1 1 280px;
      position: relative;
    }

    .search-wrap input,
    .search-wrap textarea {
      width: 100%;
      padding: 13px 14px;
      border: 1px solid var(--border);
      background: rgba(255, 255, 255, 0.08);
      color: var(--text);
      outline: none;
    }

    .search-wrap input {
      border-radius: 999px;
    }

    .search-wrap textarea {
      min-height: 170px;
      border-radius: 24px;
      resize: vertical;
      line-height: 1.55;
    }

    .search-wrap input:focus,
    .search-wrap textarea:focus {
      border-color: rgba(255, 255, 255, 0.28);
      box-shadow: 0 0 0 4px rgba(255, 255, 255, 0.05);
    }

    .status-line,
    .helper-note {
      margin-bottom: 16px;
      color: #d3d3d3;
      line-height: 1.55;
    }

    .helper-note {
      padding: 14px 16px;
      border-radius: 18px;
      background: var(--panel-soft);
      border: 1px solid rgba(255, 255, 255, 0.08);
    }

    .grid {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(220px, 1fr));
      gap: 16px;
    }

    .card {
      position: relative;
      min-height: 320px;
      overflow: hidden;
      border-radius: 22px;
      background:
        linear-gradient(180deg, rgba(255, 255, 255, 0.08), rgba(255, 255, 255, 0.02)),
        #151515;
      border: 1px solid rgba(255, 255, 255, 0.08);
      color: inherit;
      padding: 0;
      display: flex;
      flex-direction: column;
      justify-content: flex-end;
      text-align: left;
      box-shadow: 0 18px 45px rgba(0, 0, 0, 0.24);
      cursor: pointer;
      transition: transform 0.18s ease;
    }

    .card:hover {
      transform: translateY(-4px);
    }

    .card:focus-visible {
      outline: 2px solid rgba(255, 255, 255, 0.65);
      outline-offset: 3px;
    }

    .card-media,
    .card-preview {
      position: absolute;
      inset: 0;
      width: 100%;
      height: 100%;
      object-fit: cover;
      display: block;
      background: linear-gradient(135deg, #2a2a2a, #101010);
    }

    .card-preview {
      z-index: 1;
    }

    .card-fallback {
      position: absolute;
      inset: 0;
      display: grid;
      place-items: center;
      padding: 20px;
      text-align: center;
      background:
        radial-gradient(circle at top, rgba(229, 9, 20, 0.32), transparent 40%),
        linear-gradient(135deg, #262626, #0d0d0d);
      color: #f0f0f0;
      font-size: 1.05rem;
    }

    .card::after {
      content: "";
      position: absolute;
      inset: 0;
      background: linear-gradient(to top, rgba(0, 0, 0, 0.88), rgba(0, 0, 0, 0.12) 62%);
      z-index: 2;
    }

    .card-copy {
      position: relative;
      z-index: 3;
      padding: 18px;
      display: flex;
      flex-direction: column;
      gap: 10px;
    }

    .badge {
      display: inline-flex;
      width: fit-content;
      padding: 7px 10px;
      border-radius: 999px;
      background: rgba(255, 255, 255, 0.14);
      border: 1px solid rgba(255, 255, 255, 0.08);
      font-size: 0.78rem;
      letter-spacing: 0.08em;
      text-transform: uppercase;
    }

    .card h3 {
      font-size: 1.16rem;
      line-height: 1.2;
    }

    .card p {
      color: #d8d8d8;
      font-size: 0.95rem;
      line-height: 1.45;
    }

    .card-actions {
      display: flex;
      flex-wrap: wrap;
      gap: 8px;
      margin-top: 2px;
    }

    .card-chip {
      background: rgba(255, 255, 255, 0.12);
      color: white;
      border: 1px solid rgba(255, 255, 255, 0.12);
    }

    .progress {
      width: 100%;
      height: 6px;
      border-radius: 999px;
      background: rgba(255, 255, 255, 0.12);
      overflow: hidden;
    }

    .progress span {
      display: block;
      height: 100%;
      background: var(--accent);
      border-radius: 999px;
    }

    .empty {
      padding: 36px;
      border-radius: 22px;
      background: rgba(255, 255, 255, 0.05);
      border: 1px dashed rgba(255, 255, 255, 0.16);
      color: var(--muted);
      text-align: center;
    }

    .asset-grid,
    .suggestion-grid {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(220px, 1fr));
      gap: 16px;
    }

    .asset-card,
    .suggestion-card,
    .chat-output {
      border-radius: 22px;
      background:
        linear-gradient(180deg, rgba(255, 255, 255, 0.06), rgba(255, 255, 255, 0.02)),
        #121212;
      border: 1px solid rgba(255, 255, 255, 0.08);
      box-shadow: 0 18px 45px rgba(0, 0, 0, 0.2);
    }

    .asset-card {
      overflow: hidden;
    }

    .asset-preview {
      min-height: 220px;
      display: grid;
      place-items: center;
      padding: 18px;
      background:
        radial-gradient(circle at top, rgba(229, 9, 20, 0.18), transparent 34%),
        linear-gradient(135deg, #191919, #0d0d0d);
      border-bottom: 1px solid rgba(255, 255, 255, 0.08);
    }

    .asset-preview img {
      max-width: 100%;
      max-height: 280px;
      object-fit: contain;
      image-rendering: pixelated;
      image-rendering: crisp-edges;
    }

    .asset-copy,
    .suggestion-card {
      padding: 18px;
    }

    .asset-copy {
      display: flex;
      flex-direction: column;
      gap: 10px;
    }

    .asset-copy h3,
    .suggestion-card h3 {
      font-size: 1.05rem;
      line-height: 1.25;
    }

    .asset-copy p,
    .suggestion-card p {
      color: #d6d6d6;
      line-height: 1.5;
    }

    .asset-actions,
    .suggestion-actions {
      display: flex;
      flex-wrap: wrap;
      gap: 10px;
      margin-top: 4px;
    }

    .download-link {
      display: inline-flex;
      align-items: center;
      justify-content: center;
      min-height: 44px;
      padding: 12px 18px;
      border-radius: 999px;
      background: var(--accent);
      color: white;
      text-decoration: none;
      font-weight: 700;
    }

    .surface-note {
      margin-bottom: 16px;
      padding: 14px 16px;
      border-radius: 18px;
      background: rgba(255, 255, 255, 0.04);
      border: 1px solid rgba(255, 255, 255, 0.08);
      color: #dddddd;
      line-height: 1.55;
    }

    .chat-output {
      min-height: 180px;
      padding: 18px;
      white-space: pre-wrap;
      line-height: 1.62;
      color: #f2f2f2;
    }

    .creator-layout {
      display: grid;
      grid-template-columns: minmax(280px, 0.88fr) minmax(0, 1.12fr);
      gap: 18px;
      align-items: start;
    }

    .upload-form,
    .upload-catalog {
      padding: 20px;
      border: 1px solid rgba(255, 255, 255, 0.09);
      border-radius: 22px;
      background: rgba(255, 255, 255, 0.035);
    }

    .upload-form {
      display: flex;
      flex-direction: column;
      gap: 13px;
    }

    .upload-form h3,
    .upload-catalog h3 {
      font-size: 1.1rem;
    }

    .upload-form > p,
    .upload-catalog > p {
      color: var(--muted);
      font-size: 0.93rem;
      line-height: 1.5;
    }

    .upload-file-picker {
      display: grid;
      gap: 8px;
      padding: 17px;
      border: 1px dashed rgba(255, 255, 255, 0.25);
      border-radius: 18px;
      background: linear-gradient(135deg, rgba(229, 9, 20, 0.13), rgba(139, 92, 246, 0.1));
      cursor: pointer;
    }

    .upload-file-picker strong {
      font-size: 0.98rem;
    }

    .upload-file-picker span {
      color: #d1d1d1;
      font-size: 0.86rem;
      line-height: 1.45;
    }

    .upload-file-picker input {
      width: 100%;
      color: var(--muted);
      font-size: 0.84rem;
    }

    .upload-split {
      display: grid;
      grid-template-columns: minmax(0, 1fr) 132px;
      gap: 12px;
    }

    .upload-field {
      display: grid;
      gap: 7px;
      color: #dedede;
      font-size: 0.84rem;
      font-weight: 700;
    }

    .upload-field input,
    .upload-field textarea {
      width: 100%;
      padding: 12px 13px;
      border: 1px solid var(--border);
      border-radius: 14px;
      outline: none;
      background: rgba(255, 255, 255, 0.075);
      color: var(--text);
      font: inherit;
      font-weight: 400;
    }

    .upload-field textarea {
      min-height: 88px;
      resize: vertical;
    }

    .upload-field input:focus,
    .upload-field textarea:focus {
      border-color: rgba(255, 255, 255, 0.32);
      box-shadow: 0 0 0 4px rgba(255, 255, 255, 0.045);
    }

    .upload-hint {
      color: #9f9f9f;
      font-size: 0.79rem;
      line-height: 1.45;
    }

    .upload-grid {
      display: grid;
      grid-template-columns: repeat(auto-fill, minmax(210px, 1fr));
      gap: 14px;
      margin-top: 15px;
    }

    .upload-card {
      display: flex;
      min-height: 238px;
      flex-direction: column;
      overflow: hidden;
      border: 1px solid rgba(255, 255, 255, 0.09);
      border-radius: 19px;
      background: linear-gradient(165deg, rgba(255, 255, 255, 0.08), rgba(255, 255, 255, 0.02));
    }

    .upload-card-top {
      display: flex;
      min-height: 78px;
      align-items: flex-start;
      justify-content: space-between;
      gap: 12px;
      padding: 15px;
      background:
        radial-gradient(circle at 12% 0%, rgba(255, 255, 255, 0.22), transparent 28%),
        linear-gradient(135deg, rgba(229, 9, 20, 0.58), rgba(139, 92, 246, 0.52));
    }

    .upload-extension {
      display: grid;
      min-width: 52px;
      min-height: 42px;
      place-items: center;
      padding: 6px;
      border: 1px solid rgba(255, 255, 255, 0.19);
      border-radius: 13px;
      background: rgba(9, 9, 9, 0.28);
      color: white;
      font-size: 0.73rem;
      font-weight: 900;
      letter-spacing: 0.04em;
      text-transform: uppercase;
    }

    .price-chip {
      padding: 7px 10px;
      border-radius: 999px;
      background: rgba(7, 7, 7, 0.6);
      border: 1px solid rgba(255, 255, 255, 0.17);
      color: white;
      font-size: 0.8rem;
      font-weight: 800;
      white-space: nowrap;
    }

    .price-chip.free {
      color: #d4ffdb;
      background: rgba(20, 122, 61, 0.42);
    }

    .upload-card-copy {
      display: flex;
      flex: 1;
      flex-direction: column;
      padding: 15px;
    }

    .upload-card-copy h4 {
      overflow: hidden;
      font-size: 1rem;
      line-height: 1.28;
      text-overflow: ellipsis;
      white-space: nowrap;
    }

    .upload-card-copy p {
      display: -webkit-box;
      overflow: hidden;
      min-height: 42px;
      margin-top: 7px;
      color: var(--muted);
      font-size: 0.86rem;
      line-height: 1.48;
      -webkit-box-orient: vertical;
      -webkit-line-clamp: 2;
    }

    .upload-meta {
      margin-top: auto;
      padding-top: 14px;
      color: #aeaeae;
      font-size: 0.78rem;
      line-height: 1.45;
    }

    .upload-card .download-link {
      width: 100%;
      min-height: 39px;
      margin-top: 13px;
      padding: 9px 13px;
      font-size: 0.86rem;
    }



    .auth-grid {
      display: grid;
      grid-template-columns: repeat(2, minmax(0, 1fr));
      gap: 16px;
    }

    .auth-card,
    .chat-pane {
      padding: 20px;
      border: 1px solid rgba(255, 255, 255, 0.1);
      border-radius: 22px;
      background: linear-gradient(160deg, rgba(255, 255, 255, 0.075), rgba(255, 255, 255, 0.025));
    }

    .auth-card {
      display: grid;
      gap: 13px;
    }

    .auth-card h3,
    .chat-pane h3 {
      font-size: 1.08rem;
    }

    .auth-card p,
    .chat-pane-head p {
      color: var(--muted);
      font-size: 0.9rem;
      line-height: 1.48;
    }

    .auth-field {
      display: grid;
      gap: 7px;
      color: #dedede;
      font-size: 0.84rem;
      font-weight: 700;
    }

    .auth-field input,
    .chat-compose textarea {
      width: 100%;
      padding: 12px 13px;
      border: 1px solid var(--border);
      border-radius: 14px;
      outline: none;
      background: rgba(255, 255, 255, 0.075);
      color: var(--text);
      font: inherit;
      font-weight: 400;
    }

    .auth-field input:focus,
    .chat-compose textarea:focus {
      border-color: rgba(255, 255, 255, 0.34);
      box-shadow: 0 0 0 4px rgba(255, 255, 255, 0.045);
    }

    .profile-surface {
      display: flex;
      flex-wrap: wrap;
      align-items: center;
      justify-content: space-between;
      gap: 20px;
      padding: 20px;
      border: 1px solid rgba(255, 255, 255, 0.1);
      border-radius: 22px;
      background: linear-gradient(135deg, rgba(229, 9, 20, 0.16), rgba(139, 92, 246, 0.14));
    }

    .profile-summary,
    .profile-actions {
      display: flex;
      align-items: center;
      gap: 13px;
    }

    .profile-actions {
      flex-wrap: wrap;
      justify-content: flex-end;
    }

    .profile-copy {
      display: grid;
      gap: 4px;
    }

    .profile-copy span {
      color: #d5d5d5;
      font-size: 0.88rem;
    }

    .avatar {
      position: relative;
      display: grid;
      flex: 0 0 auto;
      width: 42px;
      height: 42px;
      overflow: hidden;
      place-items: center;
      border: 1px solid rgba(255, 255, 255, 0.24);
      border-radius: 50%;
      background: linear-gradient(135deg, var(--accent), #7c3aed);
      color: white;
      font-weight: 900;
      text-transform: uppercase;
    }

    .avatar-large {
      width: 62px;
      height: 62px;
      font-size: 1.35rem;
    }

    .avatar img {
      position: absolute;
      inset: 0;
      width: 100%;
      height: 100%;
      object-fit: cover;
    }

    .profile-picture-picker {
      max-width: 218px;
      color: #eeeeee;
      font-size: 0.82rem;
    }

    .chat-layout {
      display: grid;
      grid-template-columns: minmax(0, 1.15fr) minmax(280px, 0.85fr);
      gap: 18px;
    }

    .chat-pane {
      display: flex;
      min-height: 470px;
      flex-direction: column;
      gap: 14px;
    }

    .chat-pane-head {
      display: flex;
      align-items: flex-start;
      justify-content: space-between;
      gap: 12px;
    }

    .chat-messages {
      display: flex;
      min-height: 230px;
      max-height: 365px;
      flex: 1;
      flex-direction: column;
      gap: 10px;
      overflow-y: auto;
      padding-right: 4px;
    }

    .chat-message {
      display: grid;
      grid-template-columns: 38px minmax(0, 1fr);
      gap: 9px;
      padding: 11px;
      border: 1px solid rgba(255, 255, 255, 0.075);
      border-radius: 16px;
      background: rgba(255, 255, 255, 0.042);
    }

    .chat-message.mine {
      border-color: rgba(229, 9, 20, 0.34);
      background: rgba(229, 9, 20, 0.11);
    }

    .chat-message .avatar {
      width: 38px;
      height: 38px;
      font-size: 0.78rem;
    }

    .chat-message-copy {
      min-width: 0;
    }

    .chat-message-meta {
      display: flex;
      align-items: baseline;
      justify-content: space-between;
      gap: 9px;
      color: #ababab;
      font-size: 0.75rem;
    }

    .chat-message-meta strong {
      overflow: hidden;
      color: white;
      font-size: 0.84rem;
      text-overflow: ellipsis;
      white-space: nowrap;
    }

    .chat-message-text {
      margin-top: 5px;
      color: #f1f1f1;
      line-height: 1.45;
      overflow-wrap: anywhere;
    }

    .chat-compose {
      display: grid;
      grid-template-columns: minmax(0, 1fr) auto;
      gap: 10px;
      align-items: end;
    }

    .chat-compose textarea {
      min-height: 48px;
      max-height: 120px;
      resize: vertical;
    }

    .direct-user-list {
      display: flex;
      gap: 8px;
      overflow-x: auto;
      padding-bottom: 4px;
    }

    .direct-user {
      display: flex;
      flex: 0 0 auto;
      align-items: center;
      gap: 8px;
      min-width: 130px;
      padding: 8px 10px;
      border: 1px solid rgba(255, 255, 255, 0.1);
      border-radius: 14px;
      background: rgba(255, 255, 255, 0.045);
      color: white;
      text-align: left;
    }

    .direct-user.active {
      border-color: rgba(229, 9, 20, 0.65);
      background: rgba(229, 9, 20, 0.16);
    }

    .direct-user .avatar {
      width: 30px;
      height: 30px;
      font-size: 0.68rem;
    }

    .direct-user span:last-child {
      max-width: 130px;
      overflow: hidden;
      text-overflow: ellipsis;
      white-space: nowrap;
    }

    .chat-empty {
      margin: auto 0;
      padding: 21px;
      border: 1px dashed rgba(255, 255, 255, 0.17);
      border-radius: 16px;
      color: var(--muted);
      text-align: center;
      line-height: 1.5;
    }

    [hidden] {
      display: none !important;
    }

    #player {
      display: none;
      position: fixed;
      inset: 0;
      z-index: 1000;
      padding: 24px;
      background: rgba(0, 0, 0, 0.88);
      backdrop-filter: blur(10px);
    }

    .player-shell {
      position: relative;
      width: min(1200px, 100%);
      height: min(80vh, 720px);
      margin: 60px auto 0;
      border-radius: 24px;
      overflow: hidden;
      background: black;
      box-shadow: 0 24px 60px rgba(0, 0, 0, 0.45);
    }

    #video,
    #youtubeFrame {
      width: 100%;
      height: 100%;
      border: 0;
      display: none;
      background: black;
    }

    #close {
      position: absolute;
      top: 18px;
      right: 18px;
      z-index: 1001;
    }

    footer {
      margin-top: 30px;
      text-align: center;
      color: #898989;
      font-size: 0.92rem;
    }

    @media (max-width: 780px) {
      header,
      .section-head {
        flex-direction: column;
        align-items: stretch;
      }

      .hero {
        min-height: 300px;
        padding: 24px;
      }

      .spotlight {
        grid-template-columns: 1fr;
        gap: 18px;
        padding: 22px;
      }

      .creator-layout,
      .auth-grid,
      .chat-layout {
        grid-template-columns: 1fr;
      }

      .launch-grid {
        grid-template-columns: repeat(2, minmax(0, 1fr));
      }

      .panel {
        padding: 18px;
      }

      #player {
        padding: 12px;
      }

      .player-shell {
        height: min(64vh, 520px);
        margin-top: 72px;
      }

      .launch-grid {
        grid-template-columns: 1fr;
      }

      .upload-split,
      .chat-compose {
        grid-template-columns: 1fr;
      }

      .profile-surface,
      .profile-summary,
      .profile-actions {
        align-items: flex-start;
        flex-direction: column;
      }
    }

    .socials-panel { margin-top: 18px; display: grid; gap: 16px; padding: 20px; border: 1px solid rgba(255,255,255,.1); border-radius: 22px; background: rgba(255,255,255,.035); }
    .social-grid { display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 12px; }
    .social-card { display:flex; justify-content:space-between; align-items:center; gap:12px; padding:16px; border:1px solid rgba(255,255,255,.1); border-radius:16px; background:rgba(255,255,255,.04); }
    .social-card div { display:grid; gap:5px; min-width:0; }
    .social-card span { color:var(--muted); font-size:.82rem; overflow-wrap:anywhere; }
    .minecraft-social-box { display:grid; gap:12px; padding-top:8px; }
    .social-live { display:inline-flex; align-items:center; gap:6px; color:#ff5964 !important; font-weight:800; }
    .social-live::before { content:""; width:8px; height:8px; border-radius:50%; background:#ff3040; box-shadow:0 0 10px rgba(255,48,64,.8); }
    .member-social-row { display:flex; flex-wrap:wrap; gap:8px; margin-top:10px; }
    .social-chip { display:inline-flex; align-items:center; gap:6px; padding:7px 10px; border-radius:999px; background:rgba(255,255,255,.07); color:#eee; text-decoration:none; }
    .social-chip.live { background:rgba(229,9,20,.18); }
    @media (max-width: 850px) { .social-grid { grid-template-columns:1fr; } }
  </style>
</head>
<body>
  <header>
    <div class="brand">NOTFLIX</div>
    <div class="header-actions">
      <button id="goToAccount" class="secondary" type="button">Account</button>
      <button id="goToMinecraft" class="secondary" type="button">Minecraft</button>
      <button id="goToContinue" class="secondary" type="button">Continue</button>
      <button id="goToPlaylists" class="secondary" type="button">Playlists</button>
      <button id="goToYoutube" class="secondary" type="button">YouTube</button>
      <button id="goToUploads" class="secondary" type="button">Uploads</button>
      <button id="goToDrawings" class="secondary" type="button">Drawings</button>
      <button id="goToFeedback" class="secondary" type="button">Feedback</button>
      <button id="goToChat" class="secondary" type="button">Chat</button>
      <button id="goToLibrary" class="secondary" type="button">Library</button>
      <button id="headerLibraryRandom" class="primary" type="button">Shuffle Library</button>
    </div>
  </header>

  <main>
    <section class="hero">
      <div class="hero-content">
        <div class="eyebrow">Your personal screen, tuned for tonight</div>
        <h1>Movies, playlists, Minecraft skins, and fresh YouTube finds—in one smooth home base.</h1>
        <p>
          Keep your local library close, save your place automatically, build playlists for every mood,
          and jump from your collection to something new without the clutter.
        </p>
        <div class="hero-actions">
          <button id="heroRandomYoutube" class="primary" type="button">Discover YouTube</button>
          <button id="heroOpenMinecraft" class="secondary" type="button">Open Skin Lab</button>
          <button id="heroSearchYoutube" class="secondary" type="button">Search YouTube</button>
          <button id="heroRandomLibrary" class="ghost" type="button">Surprise Me</button>
        </div>
        <div class="hero-meta">
          <span id="libraryCount">0 titles loaded</span>
          <span id="localCount">0 local videos</span>
          <span id="youtubeCount">0 saved YouTube links</span>
        </div>
      </div>
    </section>

    <section id="spotlightSection" class="spotlight" aria-live="polite">
      <div class="spotlight-copy">
        <span class="spotlight-label">NotFlix spotlight</span>
        <h2 id="spotlightTitle">Your next watch is loading</h2>
        <p id="spotlightDescription">We will pick a title from your library as soon as it is ready.</p>
        <div class="spotlight-actions">
          <button id="spotlightPlay" class="primary" type="button" disabled>Play spotlight</button>
          <button id="spotlightRefresh" class="secondary" type="button">Pick another</button>
        </div>
      </div>
      <div class="spotlight-art">
        <img id="spotlightImage" alt="" hidden />
        <span id="spotlightType" class="spotlight-type">Library pick</span>
      </div>
    </section>

    <section id="launchSection" class="panel launch-panel">
      <div class="section-head">
        <div class="section-copy">
          <h2>Pick a lane</h2>
          <p>Everything useful is one tap away, so getting back into the good part takes no effort.</p>
        </div>
      </div>
      <div class="launch-grid">
        <article class="launch-card">
          <span class="launch-icon">▶</span>
          <h3>Keep Watching</h3>
          <p>Resume a saved title exactly where you stopped.</p>
          <button id="launchContinue" class="secondary" type="button">Open queue</button>
        </article>
        <article class="launch-card">
          <span class="launch-icon">✦</span>
          <h3>Shuffle Library</h3>
          <p>Let your collection decide what is on next.</p>
          <button id="launchShuffle" class="primary" type="button">Start a pick</button>
        </article>
        <article class="launch-card">
          <span class="launch-icon">⌘</span>
          <h3>Skin Lab</h3>
          <p>Preview, save, and download polished Minecraft skin views.</p>
          <button id="launchMinecraft" class="secondary" type="button">Open lab</button>
        </article>
        <article class="launch-card">
          <span class="launch-icon">↗</span>
          <h3>Fresh Finds</h3>
          <p>Pull a live set of YouTube videos whenever you want something new.</p>
          <button id="launchYoutube" class="secondary" type="button">Explore now</button>
        </article>
      </div>
    </section>

    <section id="uploadsSection" class="panel">
      <div class="section-head">
        <div class="section-copy">
          <h2>Creator uploads</h2>
          <p>Share your Minecraft add-ons, packs, worlds, maps, structures, skins, and other project files with the people on your NotFlix server.</p>
        </div>
      </div>

      <div class="creator-layout">
        <form id="uploadForm" class="upload-form">
          <h3>Publish something new</h3>
          <p>Uploads are linked to your signed-in NotFlix account and appear in the public creator catalog.</p>

          <label class="upload-file-picker" for="uploadFiles">
            <strong>Choose files</strong>
            <span>.mcaddon, .mcpack, .mcworld, .mctemplate, .mcfunction, .mcstructure, .mcskin, .zip, .schem, .litematic, .json, .png, or .txt</span>
            <input id="uploadFiles" type="file" accept=".mcaddon,.mcpack,.mcworld,.mctemplate,.mcfunction,.mcstructure,.mcskin,.zip,.schem,.litematic,.json,.png,.txt" multiple required />
          </label>

          <div class="upload-split">
            <label class="upload-field" for="uploadTitle">
              Title <input id="uploadTitle" name="title" type="text" maxlength="100" placeholder="Auto from file name" />
            </label>
            <label class="upload-field" for="uploadPrice">
              Price (€) <input id="uploadPrice" name="price" type="number" min="0" max="9999.99" step="0.01" inputmode="decimal" placeholder="0.00" />
            </label>
          </div>

          <label class="upload-field" for="uploadDescription">
            Description <textarea id="uploadDescription" name="description" maxlength="600" placeholder="Tell people what is included, which Minecraft version it supports, or how to use it."></textarea>
          </label>

          <div class="upload-hint">Price labels are shown in the catalog; this local server does not process payments yet.</div>
          <button id="publishUploadButton" class="primary" type="submit">Publish uploads</button>
          <div id="uploadStatus" class="status-line" aria-live="polite">Loading creator uploads...</div>
        </form>

        <div class="upload-catalog">
          <h3>Community catalog</h3>
          <p>Browse the latest shared creations and download the files you want.</p>
          <section id="uploadCards" class="upload-grid"></section>
        </div>
      </div>
    </section>

    <section id="drawingsSection" class="panel">
      <div class="section-head">
        <div class="section-copy"><h2>Community Drawing Studio</h2><p>Draw directly in your browser, save artwork to your account, and share it with everyone on this NotFlix server.</p></div>
        <div class="toolbar"><button id="drawingDownload" class="secondary" type="button">Download PNG</button></div>
      </div>
      <div class="drawing-layout">
        <div class="drawing-toolbar">
          <input id="drawingTitle" type="text" maxlength="100" placeholder="Drawing title…" />
          <label>Color <input id="drawingColor" type="color" value="#ffffff" /></label>
          <label>Size <input id="drawingSize" type="range" min="1" max="80" value="8" /></label>
          <output id="drawingSizeValue">8 px</output>
          <button id="drawingUndo" class="secondary" type="button">Undo</button>
          <button id="drawingRedo" class="secondary" type="button">Redo</button>
          <button id="drawingEraser" class="secondary" type="button">Eraser</button>
          <button id="drawingClear" class="secondary" type="button">Clear</button>
          <button id="drawingShare" class="primary" type="button">Share Drawing</button>
        </div>
        <canvas id="drawingCanvas" width="900" height="520" aria-label="Drawing canvas"></canvas>
        <div id="drawingStatus" class="status-line" aria-live="polite">Sign in to share drawings.</div>
        <div><h3>Shared artwork</h3><section id="drawingGallery" class="drawing-gallery"></section></div>
      </div>
    </section>

    <section id="feedbackSection" class="panel">
      <div class="section-head"><div class="section-copy"><h2>Website Feedback</h2><p>Tell the NotFlix team what is broken, what should change, or what feature should be added next.</p></div></div>
      <div id="feedbackGate" class="helper-note">Sign in to submit feedback. You can still browse the public feedback board below.</div>
      <div id="feedbackWorkspace" hidden>
        <textarea id="feedbackInput" maxlength="4000" placeholder="What should we improve? Be as specific as you want…"></textarea>
        <div class="feedback-compose-row"><button id="feedbackSend" class="primary" type="button">Send Feedback</button><span id="feedbackStatus" class="status-line" aria-live="polite"></span></div>
      </div>
      <div class="feedback-board-head"><div><h3>Community feedback</h3><p>Everyone can see the current status of submitted ideas and bug reports.</p></div><div id="feedbackStats" class="feedback-stats"></div></div>
      <section id="feedbackPublicList" class="feedback-list"></section>
      <div id="feedbackAdmin" class="feedback-admin" hidden>
        <div class="feedback-admin-head"><div><span class="admin-kicker">Raphuz feedback manager</span><h3>Feedback Bucketlist</h3><p>Bucket ideas, mark work in progress, cross fixed items off, or record things that will not be fixed.</p></div><button id="feedbackRefreshAdmin" class="secondary" type="button">Refresh</button></div>
        <div id="feedbackAdminList" class="feedback-list"></div>
      </div>
    </section>

    <section id="accountSection" class="panel">
      <div class="section-head">
        <div class="section-copy">
          <h2>Your NotFlix account</h2>
          <p id="accountStatus">Checking your sign-in…</p>
        </div>
      </div>

      <div id="authGuest" class="auth-grid">
        <form id="loginForm" class="auth-card">
          <h3>Welcome back</h3>
          <p>Sign in to keep your library activity, uploads, profile, and chats together.</p>
          <label class="auth-field" for="loginUsername">Username
            <input id="loginUsername" type="text" autocomplete="username" maxlength="20" required />
          </label>
          <label class="auth-field" for="loginPassword">Password
            <input id="loginPassword" type="password" autocomplete="current-password" maxlength="200" required />
          </label>
          <button class="primary" type="submit">Sign in</button>
        </form>

        <form id="registerForm" class="auth-card">
          <h3>Create an account</h3>
          <p>Pick a unique name. Usernames use 3–20 letters, numbers, or underscores.</p>
          <label class="auth-field" for="registerUsername">Unique username
            <input id="registerUsername" type="text" autocomplete="username" maxlength="20" pattern="[A-Za-z0-9_]{3,20}" required />
          </label>
          <label class="auth-field" for="registerPassword">Password
            <input id="registerPassword" type="password" autocomplete="new-password" minlength="8" maxlength="200" required />
          </label>
          <button class="primary" type="submit">Create account</button>
        </form>
      </div>

      <div id="authMember" class="profile-surface" hidden>
        <div class="profile-summary">
          <div id="profileAvatar" class="avatar avatar-large" aria-label="Your profile picture">
            <span id="profileAvatarFallback">?</span>
            <img id="profileAvatarImage" alt="" hidden />
          </div>
          <div class="profile-copy">
            <strong id="accountName">-</strong>
            <span>Signed in with a password-protected account.</span>
          </div>
        </div>
        <div class="profile-actions">
          <form id="profilePictureForm">
            <label class="profile-picture-picker" for="profilePictureInput">Profile picture
              <input id="profilePictureInput" type="file" accept=".png,.jpg,.jpeg,.webp,.gif,image/png,image/jpeg,image/webp,image/gif" />
            </label>
          </form>
          <button id="logoutButton" class="secondary" type="button">Sign out</button>
        </div>
      </div>

      <div class="helper-note">Your password is salted and hashed on this server. Your name is unique (case-insensitive), and your saved activity is tied to your signed-in account—not your IP address.</div>

      <div id="socialsPanel" class="socials-panel" hidden>
        <div class="section-copy">
          <h3>Linked accounts &amp; social status</h3>
          <p>Microsoft linking works without Entra in this build. Twitch/YouTube OAuth tokens are encrypted inside the NotFlix database and are never sent to the browser.</p>
        </div>
        <div class="social-grid">
          <article class="social-card"><div><strong>Microsoft Account</strong><span id="microsoftSocialStatus">Not linked</span></div><button id="microsoftLinkButton" class="secondary" type="button">Link Microsoft</button></article>
          <article class="social-card"><div><strong>Twitch</strong><span id="twitchSocialStatus">Not linked</span></div><button id="twitchLinkButton" class="secondary" type="button">Link Twitch</button></article>
          <article class="social-card"><div><strong>YouTube</strong><span id="youtubeSocialStatus">Not linked</span></div><button id="youtubeLinkButton" class="secondary" type="button">Link YouTube</button></article>
        </div>
        <div class="minecraft-social-box">
          <h3>Profile Minecraft names</h3>
          <div class="social-grid">
            <label class="auth-field">Java Edition<input id="socialMinecraftJava" maxlength="16" placeholder="Java username" /></label>
            <label class="auth-field">Bedrock / Xbox gamertag<input id="socialMinecraftBedrock" maxlength="40" placeholder="Bedrock gamertag" /></label>
          </div>
          <button id="saveSocialMinecraft" class="primary" type="button">Save Minecraft names</button>
        </div>
        <div id="socialStatus" class="status-line" aria-live="polite"></div>
      </div>
    </section>

    <section id="memberProfileSection" class="panel" hidden>
      <div class="section-head">
        <div class="section-copy"><h2 id="memberProfileTitle">Member profile</h2><p id="memberProfileSubtitle">Minecraft and linked social accounts.</p></div>
        <button id="closeMemberProfile" class="secondary" type="button">Back to members</button>
      </div>
      <div id="memberProfileCard" class="profile-surface"></div>
    </section>

    <section id="chatSection" class="panel">
      <div class="section-head">
        <div class="section-copy">
          <h2>Chat Area</h2>
          <p>Talk with everyone in Global Chat or pick a member for a private Direct Chat.</p>
        </div>
      </div>

      <div id="chatGate" class="helper-note">Sign in above to join Global Chat, send Direct Chats, and see member profile pictures.</div>
      <div id="chatWorkspace" class="chat-layout" hidden>
        <section class="chat-pane">
          <div class="chat-pane-head">
            <div>
              <h3>Global Chat</h3>
              <p>Messages visible to everyone with a NotFlix account.</p>
            </div>
          </div>
          <div id="globalMessages" class="chat-messages" aria-live="polite"></div>
          <form id="globalChatForm" class="chat-compose">
            <textarea id="globalChatInput" maxlength="1000" placeholder="Say something to everyone…" required></textarea>
            <button class="primary" type="submit">Send</button>
          </form>
        </section>

        <section class="chat-pane">
          <div class="chat-pane-head">
            <div>
              <h3>Direct Chat</h3>
              <p id="directChatTitle">Choose a member to start a private conversation.</p>
            </div>
          </div>
          <div id="directUserList" class="direct-user-list" aria-label="Members"></div>
          <div id="directMessages" class="chat-messages" aria-live="polite"></div>
          <form id="directChatForm" class="chat-compose">
            <textarea id="directChatInput" maxlength="1000" placeholder="Choose a member first…" required disabled></textarea>
            <button id="directChatSend" class="primary" type="submit" disabled>Send</button>
          </form>
        </section>
      </div>
    </section>

    <section id="minecraftSection" class="panel">
      <div class="section-head">
        <div class="section-copy">
          <h2>Minecraft Skin Lab</h2>
          <p>
            Save a Java Edition Minecraft name for your signed-in profile, preview multiple skin views, and download
            raw textures, heads, front renders, and more as PNG files.
          </p>
        </div>
        <div class="toolbar">
          <button id="minecraftLoadSavedButton" class="secondary" type="button">Load Saved Name</button>
        </div>
      </div>

      <div class="tool-row">
        <label class="search-wrap" for="minecraftUsername">
          <input id="minecraftUsername" type="text" placeholder="Enter a Minecraft Java name..." autocomplete="off" maxlength="16" />
        </label>
        <button id="minecraftSaveButton" class="primary" type="button">Save + Load Skin</button>
        <button id="minecraftPreviewButton" class="secondary" type="button">Preview Only</button>
      </div>

      <div id="minecraftStatus" class="status-line">Load a Minecraft account name to start downloading skin assets.</div>

      <div id="minecraftDetails" class="helper-note" hidden>
        <div class="account-pills">
          <span class="account-pill">Saved name: <strong id="minecraftSavedName">-</strong></span>
          <span class="account-pill">Loaded name: <strong id="minecraftLoadedName">-</strong></span>
          <span class="account-pill">UUID: <strong id="minecraftUuid">-</strong></span>
          <span class="account-pill">Model: <strong id="minecraftModel">-</strong></span>
          <span class="account-pill">Cape: <strong id="minecraftCape">-</strong></span>
        </div>
      </div>

      <section id="minecraftAssets" class="asset-grid"></section>
    </section>

    <section id="continueSection" class="panel">
      <div class="section-head">
        <div class="section-copy">
          <h2>Continue Watching</h2>
          <p>Pick up where this account left off.</p>
        </div>
      </div>
      <section id="continueCards" class="grid"></section>
    </section>

    <section id="watchedSection" class="panel">
      <div class="section-head">
        <div class="section-copy">
          <h2>Already Watched</h2>
          <p>Finished titles saved for this account.</p>
        </div>
      </div>
      <section id="watchedCards" class="grid"></section>
    </section>

    <section id="playlistSection" class="panel">
      <div class="section-head">
        <div class="section-copy">
          <h2>Playlists</h2>
          <p>Create playlists and save any local or YouTube title into them.</p>
        </div>
      </div>

      <div class="tool-row">
        <label class="search-wrap" for="playlistName">
          <input id="playlistName" type="text" placeholder="Create a playlist..." autocomplete="off" maxlength="80" />
        </label>
        <button id="createPlaylistButton" class="primary" type="button">Create Playlist</button>
      </div>

      <div id="playlistStatus" class="status-line">Checking saved playlists...</div>
      <div id="playlistTabs" class="pill-row"></div>
      <section id="playlistCards" class="grid"></section>
    </section>

    <section id="youtubeSection" class="panel">
      <div class="section-head">
        <div class="section-copy">
          <h2>Discover on YouTube</h2>
          <p>
            Grab a fresh set of random YouTube results, or search YouTube directly from here.
            These results are live, so this PC needs internet access while the server is running.
          </p>
        </div>
        <div class="toolbar">
          <button id="ytRandomButton" class="primary" type="button">Refresh Random</button>
        </div>
      </div>

      <div class="tool-row">
        <label class="search-wrap" for="ytSearch">
          <input id="ytSearch" type="search" placeholder="Search videos on YouTube..." autocomplete="off" />
        </label>
        <button id="ytSearchButton" class="primary" type="button">Search YT</button>
        <button id="ytResetButton" class="secondary" type="button">Back to Random</button>
      </div>

      <div id="ytStatus" class="status-line">Loading random YouTube videos...</div>
      <section id="ytCards" class="grid"></section>
    </section>

    <section id="librarySection" class="panel">
      <div class="section-head">
        <div class="section-copy">
          <h2>The Library</h2>
          <p id="resultSummary">Loading your catalog...</p>
        </div>
        <div class="toolbar">
          <button id="libraryRandomButton" class="primary" type="button">Random Library Pick</button>
        </div>
      </div>

      <div class="tool-row">
        <label class="search-wrap" for="search">
          <input id="search" type="search" placeholder="Search your saved library..." autocomplete="off" />
        </label>
        <button id="clearButton" class="secondary" type="button">Clear</button>
      </div>

      <section id="cards" class="grid"></section>
    </section>
  </main>

  <div id="player">
    <button id="close" class="secondary" type="button">Close</button>
    <div class="player-shell">
      <video id="video" controls autoplay playsinline></video>
      <iframe
        id="youtubeFrame"
        allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share"
        allowfullscreen
        referrerpolicy="strict-origin-when-cross-origin"></iframe>
    </div>
  </div>

  <footer>NotFlix personal streaming server. Library folder: __MEDIA_FOLDER__.</footer>

  <style>
    .drawing-layout{display:grid;gap:14px}.drawing-tools{display:flex;flex-wrap:wrap;gap:10px;align-items:center}.drawing-tools input[type=text]{flex:1;min-width:220px}.drawing-tools label{display:flex;align-items:center;gap:8px}.drawing-tools input[type=color]{width:48px;height:40px;padding:3px}.drawing-layout canvas{width:100%;max-width:900px;aspect-ratio:900/520;background:#101216;border:1px solid rgba(255,255,255,.12);border-radius:18px;touch-action:none;cursor:crosshair}.drawing-gallery{display:grid;grid-template-columns:repeat(auto-fill,minmax(220px,1fr));gap:16px;margin-top:18px}.drawing-card{overflow:hidden;border:1px solid rgba(255,255,255,.1);border-radius:18px;background:rgba(255,255,255,.035)}.drawing-card img{display:block;width:100%;aspect-ratio:16/10;object-fit:cover}.drawing-card-copy{padding:12px}.drawing-card-copy h3{margin:0 0 5px}.drawing-card-copy p{margin:0;opacity:.7}.feedback-list{display:grid;gap:12px;margin-top:16px}.feedback-card{padding:16px;border:1px solid rgba(255,255,255,.1);border-radius:16px;background:rgba(255,255,255,.035)}.feedback-card.fixed{opacity:.65}.feedback-card h4{margin:0 0 6px}.feedback-card p{white-space:pre-wrap}.feedback-actions{display:flex;flex-wrap:wrap;gap:8px;margin-top:10px}.feedback-badge{display:inline-block;padding:4px 8px;border-radius:999px;font-size:12px;background:rgba(255,255,255,.08);margin-right:6px}.feedback-badge.fixed{background:rgba(80,200,120,.2)}.feedback-badge.bucket{background:rgba(255,180,50,.2)}#feedbackInput{width:100%;min-height:130px;resize:vertical}.drawing-toolbar{display:flex;flex-wrap:wrap;gap:10px;align-items:center}.drawing-toolbar input[type=text]{flex:1;min-width:220px}.drawing-toolbar label{display:flex;align-items:center;gap:8px}.drawing-toolbar input[type=color]{width:48px;height:40px;padding:3px}.drawing-toolbar output{min-width:52px;opacity:.75}.feedback-compose-row,.feedback-board-head,.feedback-admin-head{display:flex;gap:14px;align-items:center;justify-content:space-between;margin-top:12px}.feedback-board-head{margin-top:28px}.feedback-admin{margin-top:28px;padding:18px;border:1px solid rgba(255,255,255,.12);border-radius:20px;background:rgba(255,255,255,.025)}.admin-kicker{font-size:12px;text-transform:uppercase;letter-spacing:.12em;opacity:.65}.feedback-stats{display:flex;flex-wrap:wrap;gap:8px}.feedback-stat{padding:8px 11px;border-radius:999px;background:rgba(255,255,255,.07);font-size:12px}
  </style>
  <script>
    let lastData = "";
    let allMovies = [];
    let filteredMovies = [];
    let spotlightItem = null;
    let publishedUploads = [];
    let isPlaying = false;
    let accountState = null;
    let csrfToken = "";
    let globalChatMessages = [];
    let directChatMessages = [];
    let chatUsers = [];
    let selectedDirectUser = "";
    let continueWatching = [];
    let watchedItems = [];
    let playlists = [];
    let minecraftState = { exists: false, username: "", updatedAt: 0 };
    let currentMinecraftProfile = null;
    let selectedPlaylistName = "";
    let currentItem = null;
    let lastLocalSavedSecond = -1;
    let lastYoutubeSavedSecond = -1;
    let youtubePlayer = null;
    let youtubeProgressTimer = null;
    let socialPollTimer = null;
    let drawingCanvas = null;
    let drawingContext = null;
    let drawingActive = false;

    let resolveYoutubeReady;
    const youtubeReady = new Promise(resolve => {
      resolveYoutubeReady = resolve;
    });

    const cards = document.getElementById("cards");
    const ytCards = document.getElementById("ytCards");
    const continueCards = document.getElementById("continueCards");
    const watchedCards = document.getElementById("watchedCards");
    const playlistCards = document.getElementById("playlistCards");
    const playlistTabs = document.getElementById("playlistTabs");
    const minecraftAssets = document.getElementById("minecraftAssets");
    const searchInput = document.getElementById("search");
    const ytSearchInput = document.getElementById("ytSearch");
    const playlistNameInput = document.getElementById("playlistName");
    const minecraftUsernameInput = document.getElementById("minecraftUsername");
    const resultSummary = document.getElementById("resultSummary");
    const ytStatus = document.getElementById("ytStatus");
    const accountStatus = document.getElementById("accountStatus");
    const authGuest = document.getElementById("authGuest");
    const authMember = document.getElementById("authMember");
    const loginForm = document.getElementById("loginForm");
    const loginUsername = document.getElementById("loginUsername");
    const loginPassword = document.getElementById("loginPassword");
    const registerForm = document.getElementById("registerForm");
    const registerUsername = document.getElementById("registerUsername");
    const registerPassword = document.getElementById("registerPassword");
    const accountName = document.getElementById("accountName");
    const profileAvatarImage = document.getElementById("profileAvatarImage");
    const profileAvatarFallback = document.getElementById("profileAvatarFallback");
    const profilePictureForm = document.getElementById("profilePictureForm");
    const profilePictureInput = document.getElementById("profilePictureInput");
    const logoutButton = document.getElementById("logoutButton");
    const chatGate = document.getElementById("chatGate");
    const chatWorkspace = document.getElementById("chatWorkspace");
    const globalMessages = document.getElementById("globalMessages");
    const globalChatForm = document.getElementById("globalChatForm");
    const globalChatInput = document.getElementById("globalChatInput");
    const directUserList = document.getElementById("directUserList");
    const directMessages = document.getElementById("directMessages");
    const directChatTitle = document.getElementById("directChatTitle");
    const directChatForm = document.getElementById("directChatForm");
    const directChatInput = document.getElementById("directChatInput");
    const directChatSend = document.getElementById("directChatSend");
    const playlistStatus = document.getElementById("playlistStatus");
    const minecraftStatus = document.getElementById("minecraftStatus");
    const socialsPanel = document.getElementById("socialsPanel");
    const microsoftSocialStatus = document.getElementById("microsoftSocialStatus");
    const twitchSocialStatus = document.getElementById("twitchSocialStatus");
    const youtubeSocialStatus = document.getElementById("youtubeSocialStatus");
    const microsoftLinkButton = document.getElementById("microsoftLinkButton");
    const twitchLinkButton = document.getElementById("twitchLinkButton");
    const youtubeLinkButton = document.getElementById("youtubeLinkButton");
    const socialMinecraftJava = document.getElementById("socialMinecraftJava");
    const socialMinecraftBedrock = document.getElementById("socialMinecraftBedrock");
    const saveSocialMinecraft = document.getElementById("saveSocialMinecraft");
    const socialStatus = document.getElementById("socialStatus");
    const memberProfileSection = document.getElementById("memberProfileSection");
    const memberProfileTitle = document.getElementById("memberProfileTitle");
    const memberProfileSubtitle = document.getElementById("memberProfileSubtitle");
    const memberProfileCard = document.getElementById("memberProfileCard");
    const closeMemberProfile = document.getElementById("closeMemberProfile");
    const minecraftDetails = document.getElementById("minecraftDetails");
    const minecraftSavedName = document.getElementById("minecraftSavedName");
    const minecraftLoadedName = document.getElementById("minecraftLoadedName");
    const minecraftUuid = document.getElementById("minecraftUuid");
    const minecraftModel = document.getElementById("minecraftModel");
    const minecraftCape = document.getElementById("minecraftCape");
    const overlay = document.getElementById("player");
    const video = document.getElementById("video");
    const frame = document.getElementById("youtubeFrame");
    const spotlightTitle = document.getElementById("spotlightTitle");
    const spotlightDescription = document.getElementById("spotlightDescription");
    const spotlightImage = document.getElementById("spotlightImage");
    const spotlightType = document.getElementById("spotlightType");
    const spotlightPlayButton = document.getElementById("spotlightPlay");
    const uploadForm = document.getElementById("uploadForm");
    const uploadFilesInput = document.getElementById("uploadFiles");
    const uploadTitleInput = document.getElementById("uploadTitle");
    const uploadDescriptionInput = document.getElementById("uploadDescription");
    const uploadPriceInput = document.getElementById("uploadPrice");
    const uploadStatus = document.getElementById("uploadStatus");
    const uploadCards = document.getElementById("uploadCards");
    const publishUploadButton = document.getElementById("publishUploadButton");

    function pluralize(count, label) {
      return count === 1 ? label : label + "s";
    }

    function scrollToSection(id) {
      document.getElementById(id).scrollIntoView({ behavior: "smooth", block: "start" });
    }
    document.getElementById("goToDrawings")?.addEventListener("click",()=>scrollToSection("drawingsSection"));
    document.getElementById("goToFeedback")?.addEventListener("click",()=>scrollToSection("feedbackSection"));

    function getItemKey(item) {
      if (!item) {
        return "";
      }

      return item.kind === "local" ? `local::${item.file}` : `youtube::${item.videoId}`;
    }

    function formatTime(totalSeconds) {
      const seconds = Math.max(0, Math.floor(Number(totalSeconds) || 0));
      const hours = Math.floor(seconds / 3600);
      const minutes = Math.floor((seconds % 3600) / 60);
      const remaining = seconds % 60;

      if (hours) {
        return `${hours}:${String(minutes).padStart(2, "0")}:${String(remaining).padStart(2, "0")}`;
      }

      return `${minutes}:${String(remaining).padStart(2, "0")}`;
    }

    function formatDate(timestamp) {
      if (!timestamp) {
        return "recently";
      }

      return new Date(Number(timestamp) * 1000).toLocaleString();
    }

    function updateCounters() {
      const localCount = allMovies.filter(item => item.kind === "local").length;
      const youtubeCount = allMovies.filter(item => item.kind === "youtube").length;

      document.getElementById("libraryCount").textContent = `${allMovies.length} ${pluralize(allMovies.length, "title")} loaded`;
      document.getElementById("localCount").textContent = `${localCount} local ${pluralize(localCount, "video")}`;
      document.getElementById("youtubeCount").textContent = `${youtubeCount} saved YouTube ${pluralize(youtubeCount, "link")}`;
    }

    function updateSummary() {
      const query = searchInput.value.trim();
      const visible = filteredMovies.length;
      const total = allMovies.length;

      if (!total) {
        resultSummary.textContent = "No titles found yet. Add an MP4 or a YouTube link file to the library folder.";
        return;
      }

      if (!query) {
        resultSummary.textContent = `Showing all ${visible} ${pluralize(visible, "title")}.`;
        return;
      }

      resultSummary.textContent = `Showing ${visible} of ${total} ${pluralize(total, "title")} for "${query}".`;
    }

    function stopPreview(card) {
      const preview = card.querySelector(".card-preview");
      if (!preview) {
        return;
      }

      preview.pause();
      preview.removeAttribute("src");
      preview.load();
      preview.remove();
    }

    function startPreview(card, item) {
      if (!item.preview || item.kind !== "local" || card.querySelector(".card-preview")) {
        return;
      }

      const preview = document.createElement("video");
      preview.className = "card-preview";
      preview.src = "/preview/" + encodeURIComponent(item.preview);
      preview.autoplay = true;
      preview.loop = true;
      preview.muted = true;
      preview.playsInline = true;
      card.prepend(preview);

      preview.play().catch(() => {});
    }

    function recordToDisplayItem(record, mode) {
      const item = { ...(record.item || record) };

      if (record.item) {
        item.position = Number(record.position || 0);
        item.duration = Number(record.duration || 0);
        item.progress = Number(record.progress || 0);
        item.updatedAt = Number(record.updatedAt || 0);
      }

      if (mode === "continue") {
        item.metaText = item.duration > 0
          ? `Resume at ${formatTime(item.position)} of ${formatTime(item.duration)}.`
          : `Resume from ${formatTime(item.position)}.`;
      } else if (mode === "watched") {
        item.metaText = `Finished ${formatDate(item.updatedAt)}.`;
      } else if (mode === "playlist") {
        item.metaText = item.description || "Saved in this playlist.";
      }

      return item;
    }

    function ensureAccountReady() {
      if (accountState && accountState.exists) {
        return true;
      }

      accountStatus.textContent = "Sign in first so NotFlix can save your activity, uploads, and chats to your account.";
      scrollToSection("accountSection");
      loginUsername.focus();
      return false;
    }

    function findContinueRecord(item) {
      const itemKey = getItemKey(item);
      return continueWatching.find(entry => getItemKey(entry.item) === itemKey) || null;
    }

    function createCard(item) {
      const card = document.createElement("article");
      card.className = "card";
      card.tabIndex = 0;
      card.setAttribute("role", "button");
      card.addEventListener("click", () => playItem(item));
      card.addEventListener("keydown", event => {
        if (event.key === "Enter" || event.key === " ") {
          event.preventDefault();
          playItem(item);
        }
      });

      if (item.logo) {
        const image = document.createElement("img");
        image.className = "card-media";
        image.src = "/logo/" + encodeURIComponent(item.logo);
        image.alt = item.title;
        card.appendChild(image);
      } else if (item.thumbnail) {
        const image = document.createElement("img");
        image.className = "card-media";
        image.src = item.thumbnail;
        image.alt = item.title;
        image.loading = "lazy";
        card.appendChild(image);
      } else {
        const fallback = document.createElement("div");
        fallback.className = "card-fallback";
        fallback.textContent = item.kind === "local" ? "Local Video" : "YouTube Video";
        card.appendChild(fallback);
      }

      const copy = document.createElement("div");
      copy.className = "card-copy";

      const badge = document.createElement("span");
      badge.className = "badge";
      badge.textContent = item.sourceLabel || "Video";
      copy.appendChild(badge);

      const title = document.createElement("h3");
      title.textContent = item.title;
      copy.appendChild(title);

      const detail = document.createElement("p");
      detail.textContent = item.metaText || item.description || (
        item.kind === "local"
          ? (item.preview ? "Includes preview on hover." : "Local video from your library.")
          : "Opens in the embedded YouTube player."
      );
      copy.appendChild(detail);

      if (typeof item.progress === "number" && item.progress > 0 && item.progress < 1) {
        const progress = document.createElement("div");
        progress.className = "progress";

        const fill = document.createElement("span");
        fill.style.width = `${Math.max(2, Math.round(item.progress * 100))}%`;
        progress.appendChild(fill);
        copy.appendChild(progress);
      }

      const actions = document.createElement("div");
      actions.className = "card-actions";

      const playlistButton = document.createElement("button");
      playlistButton.type = "button";
      playlistButton.className = "card-chip";
      playlistButton.textContent = "+ Playlist";
      playlistButton.addEventListener("click", event => {
        event.stopPropagation();
        promptAddToPlaylist(item);
      });
      actions.appendChild(playlistButton);

      copy.appendChild(actions);
      card.appendChild(copy);

      if (item.preview && item.kind === "local") {
        card.addEventListener("mouseenter", () => startPreview(card, item));
        card.addEventListener("mouseleave", () => stopPreview(card));
        card.addEventListener("blur", () => stopPreview(card));
      }

      return card;
    }

    function renderItems(container, items, emptyText, mode = "default") {
      container.innerHTML = "";

      if (!items.length) {
        const empty = document.createElement("div");
        empty.className = "empty";
        empty.textContent = emptyText;
        container.appendChild(empty);
        return;
      }

      const renderableItems = items.map(item => {
        if (mode === "continue" || mode === "watched") {
          return recordToDisplayItem(item, mode);
        }

        if (mode === "playlist") {
          return recordToDisplayItem(item, mode);
        }

        return item;
      });

      renderableItems.forEach(item => {
        container.appendChild(createCard(item));
      });
    }

    function renderContinueWatching() {
      if (!accountState || !accountState.exists) {
        renderItems(continueCards, [], "Create your account to start saving continue-watching progress.", "continue");
        return;
      }

      renderItems(
        continueCards,
        continueWatching,
        "Nothing to continue yet. Start a title and stop before the end to see it here.",
        "continue"
      );
    }

    function renderWatched() {
      if (!accountState || !accountState.exists) {
        renderItems(watchedCards, [], "Create your account to save finished titles.", "watched");
        return;
      }

      renderItems(
        watchedCards,
        watchedItems,
        "No finished titles yet. Fully watch a title to save it here.",
        "watched"
      );
    }

    function renderPlaylists(message = "") {
      playlistTabs.innerHTML = "";

      if (!accountState || !accountState.exists) {
        playlistStatus.textContent = "Create your account to save playlists.";
        renderItems(playlistCards, [], "No playlists yet.", "playlist");
        return;
      }

      if (!playlists.length) {
        selectedPlaylistName = "";
        playlistStatus.textContent = message || "Create a playlist or use + Playlist on a title.";
        renderItems(playlistCards, [], "No playlists yet. Create one to start saving titles.", "playlist");
        return;
      }

      if (!selectedPlaylistName || !playlists.some(playlist => playlist.name === selectedPlaylistName)) {
        selectedPlaylistName = playlists[0].name;
      }

      playlists.forEach(playlist => {
        const button = document.createElement("button");
        button.type = "button";
        button.className = playlist.name === selectedPlaylistName ? "pill active" : "pill secondary";
        button.textContent = `${playlist.name} (${playlist.items.length})`;
        button.addEventListener("click", () => {
          selectedPlaylistName = playlist.name;
          renderPlaylists();
        });
        playlistTabs.appendChild(button);
      });

      const activePlaylist = playlists.find(playlist => playlist.name === selectedPlaylistName);
      playlistStatus.textContent = message || `${playlists.length} ${pluralize(playlists.length, "playlist")} saved for ${accountState.username}.`;
      renderItems(
        playlistCards,
        activePlaylist ? activePlaylist.items : [],
        activePlaylist ? `No titles saved in "${activePlaylist.name}" yet.` : "No playlists yet.",
        "playlist"
      );
    }

    function createEmptyBlock(text) {
      const empty = document.createElement("div");
      empty.className = "empty";
      empty.textContent = text;
      return empty;
    }

    function getMinecraftAssetById(assetId) {
      if (!currentMinecraftProfile || !currentMinecraftProfile.assetViews) {
        return null;
      }

      return currentMinecraftProfile.assetViews.find(asset => asset.id === assetId) || null;
    }

    function renderMinecraftAssets() {
      minecraftAssets.innerHTML = "";

      if (!currentMinecraftProfile || !currentMinecraftProfile.assetViews || !currentMinecraftProfile.assetViews.length) {
        minecraftAssets.appendChild(createEmptyBlock("No Minecraft skin assets yet. Save or preview a Minecraft account name first."));
        return;
      }

      currentMinecraftProfile.assetViews.forEach(asset => {
        const card = document.createElement("article");
        card.className = "asset-card";

        const preview = document.createElement("div");
        preview.className = "asset-preview";

        const image = document.createElement("img");
        image.src = asset.previewUrl;
        image.alt = `${currentMinecraftProfile.username} ${asset.label}`;
        image.loading = "lazy";
        preview.appendChild(image);

        const copy = document.createElement("div");
        copy.className = "asset-copy";

        const badge = document.createElement("span");
        badge.className = "badge";
        badge.textContent = "Minecraft PNG";
        copy.appendChild(badge);

        const title = document.createElement("h3");
        title.textContent = asset.label;
        copy.appendChild(title);

        const detail = document.createElement("p");
        detail.textContent = asset.description;
        copy.appendChild(detail);

        const actions = document.createElement("div");
        actions.className = "asset-actions";

        const download = document.createElement("a");
        download.className = "download-link";
        download.href = asset.downloadUrl;
        download.textContent = "Download";
        actions.appendChild(download);

        copy.appendChild(actions);
        card.appendChild(preview);
        card.appendChild(copy);
        minecraftAssets.appendChild(card);
      });
    }

    function renderMinecraftPanel(statusMessage = "") {
      const savedName = minecraftState.username || "-";
      const loadedName = currentMinecraftProfile ? currentMinecraftProfile.username : "-";
      const loadedUuid = currentMinecraftProfile ? currentMinecraftProfile.uuidDashed : "-";
      const loadedModel = currentMinecraftProfile
        ? (currentMinecraftProfile.model === "slim" ? "Alex / slim" : "Steve / classic")
        : "-";
      const capeState = currentMinecraftProfile ? (currentMinecraftProfile.hasCape ? "Yes" : "No") : "-";

      minecraftSavedName.textContent = savedName;
      minecraftLoadedName.textContent = loadedName;
      minecraftUuid.textContent = loadedUuid;
      minecraftModel.textContent = loadedModel;
      minecraftCape.textContent = capeState;
      minecraftDetails.hidden = !(minecraftState.exists || currentMinecraftProfile);

      if (!minecraftUsernameInput.value && minecraftState.exists) {
        minecraftUsernameInput.value = minecraftState.username;
      }

      if (statusMessage) {
        minecraftStatus.textContent = statusMessage;
      } else if (currentMinecraftProfile) {
        minecraftStatus.textContent = `Loaded ${currentMinecraftProfile.username}. Choose a skin view below to preview or download it.`;
      } else if (minecraftState.exists) {
        minecraftStatus.textContent = `Saved Minecraft name: ${minecraftState.username}. Load it to preview or download skin files.`;
      } else {
        minecraftStatus.textContent = "Load a Minecraft account name to start downloading skin assets.";
      }

      renderMinecraftAssets();
    }

    async function loadMinecraftProfile(options = {}) {
      const {
        username = "",
        saveProfile = false,
        useSaved = false
      } = options;

      const requestedName = (username || minecraftUsernameInput.value || minecraftState.username || "").trim();
      if (!requestedName && !useSaved) {
        minecraftUsernameInput.focus();
        return;
      }

      minecraftStatus.textContent = useSaved
        ? "Loading the saved Minecraft account..."
        : (saveProfile ? `Saving and loading ${requestedName}...` : `Loading ${requestedName}...`);

      try {
        const data = saveProfile
          ? await postJson("/minecraft/profile", { username: requestedName })
          : await fetchJson(
            useSaved
              ? "/minecraft/profile"
              : "/minecraft/profile?username=" + encodeURIComponent(requestedName)
          );

        minecraftState = data.minecraft || minecraftState;
        currentMinecraftProfile = data.profile || null;

        if (currentMinecraftProfile) {
          minecraftUsernameInput.value = currentMinecraftProfile.username;
        }

        const message = saveProfile
          ? `Saved and loaded ${currentMinecraftProfile.username}.`
          : `Loaded ${currentMinecraftProfile.username}.`;

        renderMinecraftPanel(message);
      } catch (error) {
        currentMinecraftProfile = null;
        renderMinecraftPanel(error.message || "Could not load the Minecraft profile.");
        console.error(error);
      }
    }

    function initialFor(name) {
      return String(name || "?").trim().slice(0, 1).toUpperCase() || "?";
    }

    function setProfileAvatar(name, pictureUrl) {
      profileAvatarFallback.textContent = initialFor(name);
      const hasPicture = Boolean(pictureUrl);
      profileAvatarFallback.hidden = hasPicture;
      profileAvatarImage.hidden = !hasPicture;
      if (hasPicture) {
        profileAvatarImage.src = pictureUrl;
      } else {
        profileAvatarImage.removeAttribute("src");
      }
    }

    function makeAvatar(name, pictureUrl) {
      const avatar = document.createElement("div");
      avatar.className = "avatar";
      avatar.textContent = initialFor(name);
      if (pictureUrl) {
        const image = document.createElement("img");
        image.src = pictureUrl;
        image.alt = "";
        image.addEventListener("error", () => image.remove());
        avatar.appendChild(image);
      }
      return avatar;
    }

    function renderMessageList(container, messages, emptyText) {
      container.innerHTML = "";
      if (!messages.length) {
        const empty = document.createElement("div");
        empty.className = "chat-empty";
        empty.textContent = emptyText;
        container.appendChild(empty);
        return;
      }

      messages.forEach(message => {
        const row = document.createElement("article");
        const ownMessage = accountState && String(message.sender || "").toLowerCase() === String(accountState.username || "").toLowerCase();
        row.className = "chat-message" + (ownMessage ? " mine" : "");
        const avatar = makeAvatar(message.sender, message.senderPictureUrl);
        const copy = document.createElement("div");
        copy.className = "chat-message-copy";
        const meta = document.createElement("div");
        meta.className = "chat-message-meta";
        const sender = document.createElement("strong");
        sender.textContent = message.sender || "Member";
        const time = document.createElement("span");
        time.textContent = formatDate(message.createdAt);
        const text = document.createElement("div");
        text.className = "chat-message-text";
        text.textContent = message.text || "";
        meta.append(sender, time);
        copy.append(meta, text);
        row.append(avatar, copy);
        container.appendChild(row);
      });
      container.scrollTop = container.scrollHeight;
    }

    let drawingHistory = [];
    let drawingRedoStack = [];
    let drawingEraserMode = false;
    function snapshotDrawing(){return drawingCanvas?drawingCanvas.toDataURL("image/png"):"";}
    function restoreDrawing(dataUrl){if(!dataUrl||!drawingContext)return;const image=new Image();image.onload=()=>drawingContext.drawImage(image,0,0,drawingCanvas.width,drawingCanvas.height);image.src=dataUrl;}
    function pushDrawingHistory(){const snap=snapshotDrawing();if(!snap)return;if(!drawingHistory.length||drawingHistory[drawingHistory.length-1]!==snap)drawingHistory.push(snap);if(drawingHistory.length>30)drawingHistory.shift();drawingRedoStack=[];}
    function clearDrawingCanvas(){drawingContext.save();drawingContext.globalCompositeOperation="source-over";drawingContext.fillStyle="#101216";drawingContext.fillRect(0,0,drawingCanvas.width,drawingCanvas.height);drawingContext.restore();}
    function setupDrawingCanvas(){
      drawingCanvas=document.getElementById("drawingCanvas");if(!drawingCanvas)return;drawingContext=drawingCanvas.getContext("2d");clearDrawingCanvas();drawingHistory=[snapshotDrawing()];drawingRedoStack=[];
      const point=event=>{const rect=drawingCanvas.getBoundingClientRect();return{x:(event.clientX-rect.left)*drawingCanvas.width/rect.width,y:(event.clientY-rect.top)*drawingCanvas.height/rect.height};};
      const finish=()=>{if(!drawingActive)return;drawingActive=false;pushDrawingHistory();};
      drawingCanvas.addEventListener("pointerdown",event=>{drawingActive=true;drawingCanvas.setPointerCapture(event.pointerId);const p=point(event);drawingContext.beginPath();drawingContext.moveTo(p.x,p.y);drawingContext.strokeStyle=document.getElementById("drawingColor").value;drawingContext.lineWidth=Number(document.getElementById("drawingSize").value);drawingContext.lineCap="round";drawingContext.lineJoin="round";drawingContext.globalCompositeOperation=drawingEraserMode?"destination-out":"source-over";});
      drawingCanvas.addEventListener("pointermove",event=>{if(!drawingActive)return;const p=point(event);drawingContext.lineTo(p.x,p.y);drawingContext.stroke();});
      ["pointerup","pointercancel","pointerleave"].forEach(type=>drawingCanvas.addEventListener(type,finish));
      document.getElementById("drawingClear")?.addEventListener("click",()=>{pushDrawingHistory();clearDrawingCanvas();pushDrawingHistory();});
      document.getElementById("drawingEraser")?.addEventListener("click",event=>{drawingEraserMode=!drawingEraserMode;event.currentTarget.textContent=drawingEraserMode?"Brush":"Eraser";});
      document.getElementById("drawingUndo")?.addEventListener("click",()=>{if(drawingHistory.length<=1)return;drawingRedoStack.push(drawingHistory.pop());restoreDrawing(drawingHistory[drawingHistory.length-1]);});
      document.getElementById("drawingRedo")?.addEventListener("click",()=>{const next=drawingRedoStack.pop();if(!next)return;drawingHistory.push(next);restoreDrawing(next);});
      const size=document.getElementById("drawingSize"),sizeValue=document.getElementById("drawingSizeValue");size?.addEventListener("input",()=>{sizeValue.textContent=`${size.value} px`;});
      document.getElementById("drawingDownload")?.addEventListener("click",()=>{const a=document.createElement("a");a.href=drawingCanvas.toDataURL("image/png");a.download=(document.getElementById("drawingTitle").value.trim()||"notflix-drawing")+".png";a.click();});
      document.getElementById("drawingShare")?.addEventListener("click",shareDrawing);
    }

    async function loadDrawings() {
      const gallery=document.getElementById("drawingGallery"); if(!gallery)return;
      try { const data=await fetchJson("/drawings"); gallery.innerHTML=""; if(!data.items?.length){gallery.innerHTML='<div class="helper-note">No shared drawings yet.</div>';return;} data.items.forEach(item=>{const card=document.createElement("article");card.className="drawing-card";const img=document.createElement("img");img.src="/drawings/image/"+encodeURIComponent(item.file);img.alt=item.title;const copy=document.createElement("div");copy.className="drawing-card-copy";const h=document.createElement("h3");h.textContent=item.title;const p=document.createElement("p");p.textContent=`by ${item.author} · ${formatDate(item.createdAt)}`;copy.append(h,p);card.append(img,copy);gallery.appendChild(card);}); } catch(error){gallery.innerHTML='<div class="helper-note">Could not load shared drawings.</div>';}
    }

    async function shareDrawing() {
      const status=document.getElementById("drawingStatus");
      if(!accountState?.exists){status.textContent="Sign in before sharing a drawing.";return;}
      try { status.textContent="Sharing drawing..."; const data=await postJson("/drawings",{title:document.getElementById("drawingTitle").value,image:drawingCanvas.toDataURL("image/jpeg",0.82)}); status.textContent=`Shared “${data.drawing.title}”.`; loadDrawings(); } catch(error){status.textContent=error.message||"Could not share drawing.";}
    }

    function renderFeedbackItem(item,admin=false){const card=document.createElement("article");card.className="feedback-card"+(item.fixed?" fixed":"");const h=document.createElement("h4");h.textContent=`${item.author} · ${formatDate(item.createdAt)}`;const badges=document.createElement("div");const status=document.createElement("span");status.className="feedback-badge";status.textContent=item.fixed?"Fixed":(item.status||"open").replace("_"," ");badges.appendChild(status);if(item.bucketlisted){const b=document.createElement("span");b.className="feedback-badge bucket";b.textContent="Bucketlist";badges.appendChild(b);}const p=document.createElement("p");p.textContent=item.message;card.append(h,badges,p);if(admin){const actions=document.createElement("div");actions.className="feedback-actions";[[item.bucketlisted?"Remove from bucketlist":"Bucketlist",{bucketlisted:!item.bucketlisted}],[item.fixed?"Unfix":"Cross off as fixed",{fixed:!item.fixed}],[item.status==="in_progress"?"Mark open":"In progress",{status:item.status==="in_progress"?"open":"in_progress"}],[item.status==="wont_fix"?"Reopen":"Won't fix",{status:item.status==="wont_fix"?"open":"wont_fix"}]].forEach(([label,payload])=>{const b=document.createElement("button");b.className="secondary";b.type="button";b.textContent=label;b.addEventListener("click",()=>updateFeedback(item.id,payload));actions.appendChild(b);});card.appendChild(actions);}return card;}
    function renderFeedbackStats(items){const stats=document.getElementById("feedbackStats");if(!stats)return;const bucket=items.filter(x=>x.bucketlisted).length,fixed=items.filter(x=>x.fixed||x.status==="fixed").length,progress=items.filter(x=>x.status==="in_progress").length,open=items.filter(x=>!x.fixed&&x.status!=="wont_fix"&&x.status!=="in_progress").length;stats.innerHTML="";[["Open",open],["In progress",progress],["Bucketlist",bucket],["Fixed",fixed]].forEach(([label,value])=>{const el=document.createElement("span");el.className="feedback-stat";el.textContent=`${label}: ${value}`;stats.appendChild(el);});}
    async function loadFeedback(){const publicList=document.getElementById("feedbackPublicList"),adminBox=document.getElementById("feedbackAdmin"),adminList=document.getElementById("feedbackAdminList");try{const data=await fetchJson("/feedback"),items=data.items||[];renderFeedbackStats(items);publicList.innerHTML="";if(!items.length)publicList.innerHTML='<div class="helper-note">No feedback yet. Be the first to suggest something!</div>';items.forEach(item=>publicList.appendChild(renderFeedbackItem(item,false)));if(data.admin){adminBox.hidden=false;adminList.innerHTML="";items.forEach(item=>adminList.appendChild(renderFeedbackItem(item,true)));}else{adminBox.hidden=true;}}catch(error){publicList.innerHTML='<div class="helper-note">Could not load feedback.</div>';}}

    async function updateFeedback(id, payload) { try { await postJson("/feedback/update",{id,...payload}); loadFeedback(); } catch(error){alert(error.message||"Could not update feedback.");} }

    async function submitFeedback() { const input=document.getElementById("feedbackInput"),status=document.getElementById("feedbackStatus"); if(!accountState?.exists){status.textContent="Sign in before sending feedback.";return;} try{await postJson("/feedback",{message:input.value});input.value="";status.textContent="Feedback sent.";loadFeedback();}catch(error){status.textContent=error.message||"Could not send feedback.";} }

    function renderSocials() {
      const socials = accountState?.socials || {};
      socialsPanel.hidden = !accountState?.exists;
      const ms = socials.microsoft || {};
      const tw = socials.twitch || {};
      const yt = socials.youtube || {};
      microsoftSocialStatus.textContent = ms.linked ? (ms.displayName || "Linked") : "Not linked";
      twitchSocialStatus.textContent = tw.linked ? (tw.live ? "LIVE · " + (tw.displayName || tw.username) : (tw.displayName || tw.username || "Linked")) : "Not linked";
      twitchSocialStatus.className = tw.live ? "social-live" : "";
      youtubeSocialStatus.textContent = yt.linked ? (yt.live ? "LIVE · " + (yt.channelName || "YouTube") : (yt.channelName || "Linked")) : "Not linked";
      youtubeSocialStatus.className = yt.live ? "social-live" : "";
      socialMinecraftJava.value = socials.minecraft?.java || "";
      socialMinecraftBedrock.value = socials.minecraft?.bedrock || "";
    }

    async function refreshSocialStatus() {
      if (!accountState?.exists) return;
      try {
        const data = await fetchJson("/socials/status");
        accountState.socials = data.socials || accountState.socials;
        renderSocials();
        renderDirectUsers();
      } catch (error) { console.error(error); }
    }

    async function linkMicrosoft() {
      const displayName = window.prompt("Microsoft display name / Gamertag:", accountState?.socials?.microsoft?.displayName || "");
      if (displayName === null) return;
      const email = window.prompt("Microsoft email (optional):", accountState?.socials?.microsoft?.email || "") || "";
      const accountId = window.prompt("Microsoft account ID / Gamertag ID (optional):", accountState?.socials?.microsoft?.accountId || "") || "";
      try {
        const data = await postJson("/socials/microsoft", { displayName, email, accountId });
        accountState.socials = data.socials;
        renderSocials();
        socialStatus.textContent = "Microsoft account linked without Entra.";
      } catch (error) {
        socialStatus.textContent = error.message || "Microsoft linking failed.";
      }
    }

    async function linkSocialProvider(provider) {
      try {
        const data = await postJson(`/socials/${provider}/start`, {});
        window.location.href = data.url;
      } catch (error) { socialStatus.textContent = error.message || `Could not link ${provider}.`; }
    }

    async function saveSocialMinecraftNames() {
      try {
        const data = await postJson("/socials/minecraft", { java: socialMinecraftJava.value, bedrock: socialMinecraftBedrock.value });
        accountState.socials = data.socials;
        renderSocials();
        socialStatus.textContent = "Minecraft names saved.";
      } catch (error) { socialStatus.textContent = error.message || "Could not save Minecraft names."; }
    }

    function renderMemberProfile(profile) {
      const socials = profile.socials || {};
      const minecraft = socials.minecraft || {};
      memberProfileTitle.textContent = profile.username || "Member profile";
      memberProfileSubtitle.textContent = "Minecraft usernames and linked social accounts";
      memberProfileCard.innerHTML = "";
      const summary = document.createElement("div"); summary.className = "profile-summary";
      summary.append(makeAvatar(profile.username, profile.profilePictureUrl || ""));
      const copy = document.createElement("div"); copy.className = "profile-copy";
      const name = document.createElement("strong"); name.textContent = profile.username || "Member";
      const meta = document.createElement("span"); meta.textContent = `Member since ${formatDate(profile.createdAt)}`;
      copy.append(name, meta); summary.appendChild(copy);
      const details = document.createElement("div"); details.className = "profile-copy";
      const java = document.createElement("span"); java.textContent = "Java: " + (minecraft.java || "Not linked");
      const bedrock = document.createElement("span"); bedrock.textContent = "Bedrock: " + (minecraft.bedrock || "Not linked");
      details.append(java, bedrock);
      const chips = document.createElement("div"); chips.className = "member-social-row";
      const tw = socials.twitch || {}; const yt = socials.youtube || {}; const ms = socials.microsoft || {};
      if (tw.linked) { const a=document.createElement("a"); a.className="social-chip"+(tw.live?" live":""); a.href=tw.channelUrl||"#"; a.target="_blank"; a.rel="noopener"; a.textContent=tw.live?"🔴 Twitch LIVE":`Twitch: ${tw.displayName||tw.username}`; chips.appendChild(a); }
      if (yt.linked) { const a=document.createElement("a"); a.className="social-chip"+(yt.live?" live":""); a.href=yt.channelUrl||"#"; a.target="_blank"; a.rel="noopener"; a.textContent=yt.live?"🔴 YouTube LIVE":`YouTube: ${yt.channelName||"Channel"}`; chips.appendChild(a); }
      if (ms.linked) { const span=document.createElement("span"); span.className="social-chip"; span.textContent=`Microsoft: ${ms.displayName||"Linked"}`; chips.appendChild(span); }
      memberProfileCard.append(summary, details, chips);
    }

    async function openMemberProfile(username) {
      try {
        const data = await fetchJson("/profile?user=" + encodeURIComponent(username));
        renderMemberProfile(data.profile);
        memberProfileSection.hidden = false;
        memberProfileSection.scrollIntoView({ behavior: "smooth", block: "start" });
        history.replaceState(null, "", "#profile=" + encodeURIComponent(username));
      } catch (error) { accountStatus.textContent = error.message || "Could not open member profile."; }
    }

    function renderDirectUsers() {
      directUserList.innerHTML = "";
      if (!chatUsers.length) {
        const empty = document.createElement("span");
        empty.className = "upload-hint";
        empty.textContent = "No other members have created an account yet.";
        directUserList.appendChild(empty);
        return;
      }
      chatUsers.forEach(user => {
        const button = document.createElement("button");
        button.type = "button";
        button.className = "direct-user" + (String(user.username).toLowerCase() === String(selectedDirectUser).toLowerCase() ? " active" : "");
        button.append(makeAvatar(user.username, user.profilePictureUrl));
        const label = document.createElement("span");
        label.textContent = user.username;
        label.style.cursor = "pointer";
        label.addEventListener("click", event => { event.stopPropagation(); openMemberProfile(user.username); });
        const socials = user.socials || {};
        const live = Boolean(socials.twitch?.live || socials.youtube?.live);
        if (live) {
          const badge = document.createElement("span");
          badge.className = "social-live";
          badge.style.marginLeft = "6px";
          badge.textContent = "LIVE";
          label.appendChild(badge);
        }
        button.appendChild(label);
        button.addEventListener("click", () => selectDirectUser(user.username));
        directUserList.appendChild(button);
      });
    }

    function renderChat() {
      renderMessageList(globalMessages, globalChatMessages, "Global Chat is quiet. Be the first to say hello.");
      renderDirectUsers();
      const selected = chatUsers.find(user => String(user.username).toLowerCase() === String(selectedDirectUser).toLowerCase());
      const canDirect = Boolean(selected);
      directChatTitle.textContent = canDirect
        ? `Private conversation with ${selected.username}.`
        : "Choose a member to start a private conversation.";
      directChatInput.disabled = !canDirect;
      directChatSend.disabled = !canDirect;
      directChatInput.placeholder = canDirect ? `Message ${selected.username}…` : "Choose a member first…";
      renderMessageList(directMessages, directChatMessages, canDirect ? `No messages with ${selected.username} yet.` : "Select a member above to open Direct Chat.");
    }

    async function loadGlobalChat() {
      const data = await fetchJson("/chat/global");
      globalChatMessages = data.items || [];
    }

    async function loadChatUsers() {
      const data = await fetchJson("/users");
      chatUsers = data.items || [];
      if (selectedDirectUser && !chatUsers.some(user => String(user.username).toLowerCase() === String(selectedDirectUser).toLowerCase())) {
        selectedDirectUser = "";
        directChatMessages = [];
      }
    }

    async function loadDirectChat() {
      if (!selectedDirectUser) {
        directChatMessages = [];
        return;
      }
      const data = await fetchJson("/chat/direct?with=" + encodeURIComponent(selectedDirectUser));
      directChatMessages = data.items || [];
    }

    async function loadChatData() {
      if (!accountState || !accountState.exists) {
        return;
      }
      try {
        await Promise.all([loadGlobalChat(), loadChatUsers()]);
        await loadDirectChat();
        renderChat();
      } catch (error) {
        console.error(error);
      }
    }

    async function selectDirectUser(username) {
      selectedDirectUser = username;
      directChatMessages = [];
      renderChat();
      try {
        await loadDirectChat();
        renderChat();
        directChatInput.focus();
      } catch (error) {
        directChatTitle.textContent = error.message || "Could not open that Direct Chat.";
        console.error(error);
      }
    }

    async function sendGlobalChat(event) {
      event.preventDefault();
      const text = globalChatInput.value.trim();
      if (!text) {
        globalChatInput.focus();
        return;
      }
      try {
        const data = await postJson("/chat/global", { text });
        globalChatMessages.push(data.item);
        globalChatInput.value = "";
        renderChat();
      } catch (error) {
        accountStatus.textContent = error.message || "Could not send the global message.";
      }
    }

    async function sendDirectChat(event) {
      event.preventDefault();
      const text = directChatInput.value.trim();
      if (!selectedDirectUser || !text) {
        directChatInput.focus();
        return;
      }
      try {
        const data = await postJson("/chat/direct", { recipient: selectedDirectUser, text });
        directChatMessages.push(data.item);
        directChatInput.value = "";
        renderChat();
      } catch (error) {
        directChatTitle.textContent = error.message || "Could not send the direct message.";
      }
    }

    function applyAccountState(data, statusMessage = "") {
      accountState = data || { exists: false };
      csrfToken = accountState.csrfToken || "";
      continueWatching = accountState.continueWatching || [];
      watchedItems = accountState.watched || [];
      playlists = accountState.playlists || [];
      minecraftState = accountState.minecraft || minecraftState;
      const signedIn = Boolean(accountState.exists);

      authGuest.hidden = signedIn;
      authMember.hidden = !signedIn;
      chatGate.hidden = signedIn;
      chatWorkspace.hidden = !signedIn;
      accountName.textContent = accountState.username || "-";
      setProfileAvatar(accountState.username, accountState.profilePictureUrl || "");

      if (statusMessage) {
        accountStatus.textContent = statusMessage;
      } else if (signedIn) {
        accountStatus.textContent = `Signed in as ${accountState.username}.`;
      } else {
        accountStatus.textContent = "Sign in or create a password-protected account to save your NotFlix experience.";
      }

      renderContinueWatching();
      renderWatched();
      renderPlaylists();
      renderMinecraftPanel();
      renderSocials();
      const feedbackGate = document.getElementById("feedbackGate");
      const feedbackWorkspace = document.getElementById("feedbackWorkspace");
      if (feedbackGate) feedbackGate.hidden = signedIn;
      if (feedbackWorkspace) feedbackWorkspace.hidden = !signedIn;
      loadFeedback();

      if (signedIn) {
        refreshSocialStatus();
        loadChatData();
        if (minecraftState.exists) {
          const loadedName = currentMinecraftProfile ? currentMinecraftProfile.username.toLowerCase() : "";
          if (loadedName !== minecraftState.username.toLowerCase()) {
            loadMinecraftProfile({ useSaved: true });
          }
        }
      } else {
        globalChatMessages = [];
        directChatMessages = [];
        chatUsers = [];
        selectedDirectUser = "";
      }
    }

    function formatUploadSize(bytes) {
      const value = Number(bytes) || 0;
      if (value < 1024 * 1024) {
        return `${Math.max(1, Math.round(value / 1024))} KB`;
      }
      return `${(value / (1024 * 1024)).toFixed(value >= 100 * 1024 * 1024 ? 0 : 1)} MB`;
    }

    function renderUploads(message = "") {
      uploadCards.innerHTML = "";
      uploadStatus.textContent = message || (publishedUploads.length
        ? `${publishedUploads.length} ${pluralize(publishedUploads.length, "creator upload")} available.`
        : "No uploads yet. Publish the first creation from this page.");

      if (!publishedUploads.length) {
        const empty = document.createElement("div");
        empty.className = "empty";
        empty.textContent = "No creator uploads have been published yet.";
        uploadCards.appendChild(empty);
        return;
      }

      publishedUploads.forEach(item => {
        const card = document.createElement("article");
        card.className = "upload-card";

        const top = document.createElement("div");
        top.className = "upload-card-top";
        const extension = document.createElement("span");
        extension.className = "upload-extension";
        extension.textContent = (item.extension || "file").replace(/^[.]/, "");
        const price = document.createElement("span");
        price.className = "price-chip" + (Number(item.priceCents || 0) === 0 ? " free" : "");
        price.textContent = item.priceLabel || "Free";
        top.append(extension, price);

        const copy = document.createElement("div");
        copy.className = "upload-card-copy";
        const title = document.createElement("h4");
        title.textContent = item.title || item.originalName || "Untitled upload";
        const description = document.createElement("p");
        description.textContent = item.description || "Shared through the NotFlix creator catalog.";
        const meta = document.createElement("div");
        meta.className = "upload-meta";
        meta.textContent = `By ${item.uploader || "NotFlix creator"} · ${formatUploadSize(item.size)} · ${formatDate(item.createdAt)}`;
        const download = document.createElement("a");
        download.className = "download-link";
        download.href = item.downloadUrl;
        download.textContent = Number(item.priceCents || 0) > 0 ? `Download · ${item.priceLabel}` : "Download free";
        copy.append(title, description, meta, download);
        card.append(top, copy);
        uploadCards.appendChild(card);
      });
    }

    async function loadUploads(message = "") {
      try {
        const data = await fetchJson("/uploads");
        publishedUploads = data.items || [];
        renderUploads(message);
      } catch (error) {
        uploadStatus.textContent = error.message || "Could not load creator uploads.";
        console.error(error);
      }
    }

    async function publishUploads(event) {
      event.preventDefault();
      if (!ensureAccountReady()) {
        return;
      }

      const files = Array.from(uploadFilesInput.files || []);
      if (!files.length) {
        uploadFilesInput.focus();
        return;
      }
      if (files.length > 8) {
        uploadStatus.textContent = "Choose up to 8 files at once.";
        return;
      }

      const formData = new FormData();
      files.forEach(file => formData.append("files", file));
      formData.append("title", uploadTitleInput.value.trim());
      formData.append("description", uploadDescriptionInput.value.trim());
      formData.append("price", uploadPriceInput.value.trim());

      publishUploadButton.disabled = true;
      uploadStatus.textContent = files.length === 1 ? "Publishing your upload..." : `Publishing ${files.length} uploads...`;
      try {
        const headers = csrfToken ? { "X-CSRF-Token": csrfToken } : {};
        const response = await fetch("/uploads", {
          method: "POST",
          headers,
          body: formData
        });
        const data = await response.json();
        if (!response.ok) {
          throw new Error(data.error || "Could not publish the upload.");
        }

        uploadForm.reset();
        await loadUploads(`Published ${data.items.length} ${pluralize(data.items.length, "upload")}.`);
      } catch (error) {
        uploadStatus.textContent = error.message || "Could not publish the upload.";
        console.error(error);
      } finally {
        publishUploadButton.disabled = false;
      }
    }

    function refreshSpotlight() {
      const pool = allMovies.length ? allMovies : [];

      if (!pool.length) {
        spotlightItem = null;
        spotlightTitle.textContent = "Your next watch is loading";
        spotlightDescription.textContent = "Add a title to the library and it will appear here as a ready-to-play pick.";
        spotlightType.textContent = "Library pick";
        spotlightImage.hidden = true;
        spotlightImage.removeAttribute("src");
        spotlightPlayButton.disabled = true;
        return;
      }

      spotlightItem = pool[Math.floor(Math.random() * pool.length)];
      const isLocal = spotlightItem.kind === "local";
      const imageUrl = isLocal && spotlightItem.logo
        ? "/logo/" + encodeURIComponent(spotlightItem.logo)
        : (spotlightItem.thumbnail || "");

      spotlightTitle.textContent = spotlightItem.title;
      spotlightDescription.textContent = isLocal
        ? "A saved title from your local shelf, ready when you are."
        : "A saved YouTube link from your collection, ready to play.";
      spotlightType.textContent = isLocal ? "Local library" : "YouTube saved";
      spotlightPlayButton.disabled = false;

      if (imageUrl) {
        spotlightImage.src = imageUrl;
        spotlightImage.hidden = false;
      } else {
        spotlightImage.hidden = true;
        spotlightImage.removeAttribute("src");
      }
    }

    function applyLibraryFilter() {
      const query = searchInput.value.trim().toLowerCase();
      filteredMovies = allMovies.filter(item => item.title.toLowerCase().includes(query));
      renderItems(
        cards,
        filteredMovies,
        allMovies.length
          ? "No saved titles match your search."
          : "Your library is empty. Add an MP4 or a YouTube link file to get started."
      );
      updateSummary();
    }

    function resetVideoSurface() {
      video.pause();
      video.removeAttribute("src");
      video.load();
      video.style.display = "none";
    }

    function stopYoutubeProgressLoop() {
      if (youtubeProgressTimer) {
        clearInterval(youtubeProgressTimer);
        youtubeProgressTimer = null;
      }
    }

    function startYoutubeProgressLoop() {
      stopYoutubeProgressLoop();
      youtubeProgressTimer = setInterval(() => {
        syncYoutubeProgress(false, false, false);
      }, 5000);
    }

    function resetYoutubeSurface() {
      stopYoutubeProgressLoop();

      if (youtubePlayer && typeof youtubePlayer.stopVideo === "function") {
        try {
          youtubePlayer.stopVideo();
        } catch (error) {
          console.error(error);
        }
      } else {
        frame.src = "";
      }

      frame.style.display = "none";
    }

    async function fetchJson(url) {
      const response = await fetch(url);
      const data = await response.json();

      if (!response.ok) {
        throw new Error(data.error || "Request failed.");
      }

      return data;
    }

    async function postJson(url, payload) {
      const headers = { "Content-Type": "application/json" };
      if (csrfToken) headers["X-CSRF-Token"] = csrfToken;
      const response = await fetch(url, {
        method: "POST",
        headers,
        body: JSON.stringify(payload)
      });

      const data = await response.json();
      if (!response.ok) {
        throw new Error(data.error || "Request failed.");
      }

      return data;
    }

    microsoftLinkButton?.addEventListener("click", linkMicrosoft);
    twitchLinkButton?.addEventListener("click", () => linkSocialProvider("twitch"));
    youtubeLinkButton?.addEventListener("click", () => linkSocialProvider("youtube"));
    saveSocialMinecraft?.addEventListener("click", saveSocialMinecraftNames);
    closeMemberProfile?.addEventListener("click", () => { memberProfileSection.hidden = true; history.replaceState(null, "", "#"); });

    async function loadAccount(silent = false) {
      if (!silent) {
        accountStatus.textContent = "Checking your sign-in…";
      }

      try {
        const data = await fetchJson("/auth/me");
        applyAccountState(data);
      } catch (error) {
        accountStatus.textContent = error.message || "Could not check your account.";
        console.error(error);
      }
    }

    async function authenticate(event, endpoint, usernameField, passwordField, actionLabel) {
      event.preventDefault();
      const username = usernameField.value.trim();
      const password = passwordField.value;
      if (!username || !password) {
        usernameField.focus();
        return;
      }
      accountStatus.textContent = actionLabel + "…";
      try {
        const data = await postJson(endpoint, { username, password });
        passwordField.value = "";
        if (endpoint === "/auth/register") {
          registerForm.reset();
        } else {
          loginForm.reset();
        }
        applyAccountState(data, endpoint === "/auth/register" ? `Account created. Welcome, ${data.username}.` : `Welcome back, ${data.username}.`);
      } catch (error) {
        accountStatus.textContent = error.message || "Could not sign in.";
        console.error(error);
      }
    }

    async function uploadProfilePicture() {
      const picture = profilePictureInput.files && profilePictureInput.files[0];
      if (!picture) {
        return;
      }
      const formData = new FormData();
      formData.append("profilePicture", picture);
      accountStatus.textContent = "Uploading profile picture…";
      try {
        const headers = csrfToken ? { "X-CSRF-Token": csrfToken } : {};
        const response = await fetch("/profile/picture", {
          method: "POST",
          headers,
          body: formData
        });
        const data = await response.json();
        if (!response.ok) {
          throw new Error(data.error || "Could not upload the profile picture.");
        }
        profilePictureForm.reset();
        await loadAccount(true);
        accountStatus.textContent = "Profile picture updated.";
        await loadChatData();
      } catch (error) {
        accountStatus.textContent = error.message || "Could not upload the profile picture.";
      }
    }

    async function logout() {
      try {
        const data = await postJson("/auth/logout", {});
        applyAccountState(data, "You are signed out.");
      } catch (error) {
        accountStatus.textContent = error.message || "Could not sign out.";
      }
    }

    async function savePlaylist(name, item = null) {
      const data = await postJson("/account/playlists", { name, item });
      playlists = data.playlists || [];

      const requestedName = name.trim().toLowerCase();
      const match = playlists.find(playlist => playlist.name.toLowerCase() === requestedName);
      if (match) {
        selectedPlaylistName = match.name;
      }

      return data;
    }

    async function createPlaylist() {
      if (!ensureAccountReady()) {
        return;
      }

      const name = playlistNameInput.value.trim();
      if (!name) {
        playlistNameInput.focus();
        return;
      }

      playlistStatus.textContent = `Creating "${name}"...`;

      try {
        await savePlaylist(name);
        playlistNameInput.value = "";
        renderPlaylists(`Playlist "${selectedPlaylistName}" is ready.`);
      } catch (error) {
        playlistStatus.textContent = error.message || "Could not create the playlist.";
        console.error(error);
      }
    }

    async function promptAddToPlaylist(item) {
      if (!ensureAccountReady()) {
        return;
      }

      const suggestedName = selectedPlaylistName || playlistNameInput.value.trim() || "Favorites";
      const name = window.prompt("Playlist name", suggestedName);

      if (!name || !name.trim()) {
        return;
      }

      playlistStatus.textContent = `Saving "${item.title}" to "${name.trim()}"...`;

      try {
        await savePlaylist(name, item);
        renderPlaylists(`Saved "${item.title}" to "${selectedPlaylistName}".`);
      } catch (error) {
        playlistStatus.textContent = error.message || "Could not save the title to the playlist.";
        console.error(error);
      }
    }

    async function syncLocalProgress(force = false, completed = false, refresh = false) {
      if (!accountState || !accountState.exists || !currentItem || currentItem.kind !== "local") {
        return;
      }

      const position = completed ? (video.duration || video.currentTime || 0) : (video.currentTime || 0);
      const duration = video.duration || 0;
      const wholeSeconds = Math.floor(position);

      if (!force) {
        if (wholeSeconds < 15 || duration <= 0) {
          return;
        }

        if (wholeSeconds === lastLocalSavedSecond || wholeSeconds % 5 !== 0) {
          return;
        }
      }

      lastLocalSavedSecond = wholeSeconds;

      try {
        await postJson("/account/progress", {
          item: currentItem,
          position,
          duration,
          completed
        });

        if (refresh) {
          await loadAccount(true);
        }
      } catch (error) {
        console.error(error);
      }
    }

    async function syncYoutubeProgress(force = false, completed = false, refresh = false) {
      if (!accountState || !accountState.exists || !currentItem || currentItem.kind !== "youtube") {
        return;
      }

      if (!youtubePlayer || typeof youtubePlayer.getCurrentTime !== "function") {
        return;
      }

      let position = 0;
      let duration = 0;

      try {
        position = completed ? (youtubePlayer.getDuration() || youtubePlayer.getCurrentTime() || 0) : (youtubePlayer.getCurrentTime() || 0);
        duration = youtubePlayer.getDuration() || 0;
      } catch (error) {
        console.error(error);
        return;
      }

      const wholeSeconds = Math.floor(position);

      if (!force) {
        if (wholeSeconds < 15 || duration <= 0) {
          return;
        }

        if (wholeSeconds === lastYoutubeSavedSecond || wholeSeconds % 5 !== 0) {
          return;
        }
      }

      lastYoutubeSavedSecond = wholeSeconds;

      try {
        await postJson("/account/progress", {
          item: currentItem,
          position,
          duration,
          completed
        });

        if (refresh) {
          await loadAccount(true);
        }
      } catch (error) {
        console.error(error);
      }
    }

    async function syncCurrentPlayback(force = false, completed = false, refresh = false) {
      if (!currentItem) {
        return;
      }

      if (currentItem.kind === "local") {
        await syncLocalProgress(force, completed, refresh);
        return;
      }

      await syncYoutubeProgress(force, completed, refresh);
    }

    async function closePlayer() {
      await syncCurrentPlayback(true, false, true);
      isPlaying = false;
      currentItem = null;
      resetVideoSurface();
      resetYoutubeSurface();
      overlay.style.display = "none";
      document.body.style.overflow = "";
      lastLocalSavedSecond = -1;
      lastYoutubeSavedSecond = -1;
    }

    async function playYoutubeItem(item) {
      const resumeRecord = findContinueRecord(item);
      const resumeSeconds = resumeRecord ? Math.floor(Number(resumeRecord.position || 0)) : 0;

      try {
        await Promise.race([
          youtubeReady,
          new Promise((_, reject) => {
            setTimeout(() => reject(new Error("YouTube player timed out.")), 7000);
          })
        ]);

        frame.style.display = "block";
        youtubePlayer.loadVideoById({
          videoId: item.videoId,
          startSeconds: resumeSeconds > 5 ? resumeSeconds : 0
        });
      } catch (error) {
        let fallbackUrl = item.embedUrl;
        if (resumeSeconds > 5) {
          fallbackUrl += `&start=${resumeSeconds}`;
        }

        frame.src = fallbackUrl;
        frame.style.display = "block";
      }
    }

    async function playItem(item) {
      if (!ensureAccountReady()) {
        return;
      }

      if (currentItem && isPlaying) {
        await syncCurrentPlayback(true, false, true);
      }

      isPlaying = false;
      currentItem = null;
      resetVideoSurface();
      resetYoutubeSurface();

      currentItem = item;
      lastLocalSavedSecond = -1;
      lastYoutubeSavedSecond = -1;
      isPlaying = true;
      overlay.style.display = "block";
      document.body.style.overflow = "hidden";

      if (item.kind === "youtube" && item.videoId) {
        await playYoutubeItem(item);
        return;
      }

      if (item.file) {
        video.src = "/movie/" + encodeURIComponent(item.file);
        video.style.display = "block";
        video.play().catch(() => {});
      }
    }

    function playRandomLibrary() {
      const pool = filteredMovies.length ? filteredMovies : allMovies;
      if (!pool.length) {
        return;
      }

      const item = pool[Math.floor(Math.random() * pool.length)];
      playItem(item);
    }

    async function loadRandomYoutube() {
      ytStatus.textContent = "Loading random YouTube videos...";

      try {
        const data = await fetchJson("/youtube/random");
        renderItems(ytCards, data.items, "Could not load random YouTube videos.");

        if (!data.items.length) {
          ytStatus.textContent = "No random YouTube videos were returned.";
          return;
        }

        ytStatus.textContent = `Random topic: "${data.query}" · ${data.items.length} ${pluralize(data.items.length, "video")}.`;
      } catch (error) {
        renderItems(ytCards, [], error.message || "Could not load random YouTube videos.");
        ytStatus.textContent = error.message || "Could not load random YouTube videos.";
        console.error(error);
      }
    }

    async function searchYoutube() {
      const query = ytSearchInput.value.trim();
      if (!query) {
        ytSearchInput.focus();
        return;
      }

      ytStatus.textContent = `Searching YouTube for "${query}"...`;

      try {
        const data = await fetchJson("/youtube/search?q=" + encodeURIComponent(query));
        renderItems(ytCards, data.items, `No YouTube videos found for "${query}".`);

        if (!data.items.length) {
          ytStatus.textContent = `No YouTube videos found for "${query}".`;
          return;
        }

        ytStatus.textContent = `YouTube search: "${data.query}" · ${data.items.length} ${pluralize(data.items.length, "video")}.`;
      } catch (error) {
        renderItems(ytCards, [], error.message || "YouTube search failed.");
        ytStatus.textContent = error.message || "YouTube search failed.";
        console.error(error);
      }
    }

    async function fetchMovies() {
      if (isPlaying) {
        return;
      }

      try {
        const response = await fetch("/list");
        const data = await response.text();

        if (data !== lastData) {
          lastData = data;
          allMovies = JSON.parse(data);
          updateCounters();
          applyLibraryFilter();
          refreshSpotlight();
        }
      } catch (error) {
        resultSummary.textContent = "Could not load the catalog right now.";
        console.error(error);
      }
    }

    function handleYoutubePlayerState(event) {
      if (!currentItem || currentItem.kind !== "youtube" || !window.YT || !window.YT.PlayerState) {
        return;
      }

      if (event.data === window.YT.PlayerState.PLAYING) {
        startYoutubeProgressLoop();
        return;
      }

      if (event.data === window.YT.PlayerState.PAUSED) {
        stopYoutubeProgressLoop();
        syncYoutubeProgress(true, false, true);
        return;
      }

      if (event.data === window.YT.PlayerState.ENDED) {
        stopYoutubeProgressLoop();
        syncYoutubeProgress(true, true, true);
      }
    }

    window.onYouTubeIframeAPIReady = function () {
      youtubePlayer = new window.YT.Player("youtubeFrame", {
        playerVars: {
          autoplay: 1,
          rel: 0,
          modestbranding: 1,
          playsinline: 1
        },
        events: {
          onReady: () => resolveYoutubeReady(),
          onStateChange: handleYoutubePlayerState
        }
      });
    };

    function loadYoutubeIframeApi() {
      if (document.getElementById("youtube-iframe-api")) {
        return;
      }

      const script = document.createElement("script");
      script.id = "youtube-iframe-api";
      script.src = "https://www.youtube.com/iframe_api";
      document.head.appendChild(script);
    }

    searchInput.addEventListener("input", applyLibraryFilter);
    ytSearchInput.addEventListener("keydown", event => {
      if (event.key === "Enter") {
        searchYoutube();
      }
    });

    minecraftUsernameInput.addEventListener("keydown", event => {
      if (event.key === "Enter") {
        loadMinecraftProfile({ saveProfile: true });
      }
    });

    playlistNameInput.addEventListener("keydown", event => {
      if (event.key === "Enter") {
        event.preventDefault();
        createPlaylist();
      }
    });

    video.addEventListener("loadedmetadata", () => {
      if (!currentItem || currentItem.kind !== "local") {
        return;
      }

      const resumeRecord = findContinueRecord(currentItem);
      const resumeSeconds = resumeRecord ? Number(resumeRecord.position || 0) : 0;

      if (resumeSeconds > 5 && video.duration > 0 && resumeSeconds < video.duration - 3) {
        video.currentTime = resumeSeconds;
      }
    });

    video.addEventListener("timeupdate", () => {
      syncLocalProgress(false, false, false);
    });

    video.addEventListener("pause", () => {
      if (isPlaying && currentItem && currentItem.kind === "local" && !video.ended) {
        syncLocalProgress(true, false, true);
      }
    });

    video.addEventListener("ended", () => {
      syncLocalProgress(true, true, true);
    });

    document.getElementById("clearButton").addEventListener("click", () => {
      searchInput.value = "";
      applyLibraryFilter();
      searchInput.focus();
    });

    document.getElementById("ytSearchButton").addEventListener("click", searchYoutube);
    document.getElementById("ytRandomButton").addEventListener("click", loadRandomYoutube);
    document.getElementById("ytResetButton").addEventListener("click", () => {
      ytSearchInput.value = "";
      loadRandomYoutube();
    });

    document.getElementById("createPlaylistButton").addEventListener("click", createPlaylist);
    document.getElementById("minecraftSaveButton").addEventListener("click", () => {
      loadMinecraftProfile({ saveProfile: true });
    });
    document.getElementById("minecraftPreviewButton").addEventListener("click", () => {
      loadMinecraftProfile();
    });
    document.getElementById("minecraftLoadSavedButton").addEventListener("click", () => {
      loadMinecraftProfile({ useSaved: true });
    });
    loginForm.addEventListener("submit", event => authenticate(event, "/auth/login", loginUsername, loginPassword, "Signing in"));
    registerForm.addEventListener("submit", event => authenticate(event, "/auth/register", registerUsername, registerPassword, "Creating your account"));
    profilePictureInput.addEventListener("change", uploadProfilePicture);
    logoutButton.addEventListener("click", logout);
    globalChatForm.addEventListener("submit", sendGlobalChat);
    directChatForm.addEventListener("submit", sendDirectChat);
    uploadForm.addEventListener("submit", publishUploads);

    spotlightPlayButton.addEventListener("click", () => {
      if (spotlightItem) {
        playItem(spotlightItem);
      }
    });
    document.getElementById("spotlightRefresh").addEventListener("click", refreshSpotlight);
    document.getElementById("launchContinue").addEventListener("click", () => scrollToSection("continueSection"));
    document.getElementById("launchShuffle").addEventListener("click", playRandomLibrary);
    document.getElementById("launchMinecraft").addEventListener("click", () => scrollToSection("minecraftSection"));
    document.getElementById("launchYoutube").addEventListener("click", () => {
      scrollToSection("youtubeSection");
      loadRandomYoutube();
    });

    document.getElementById("goToAccount").addEventListener("click", () => scrollToSection("accountSection"));
    document.getElementById("goToMinecraft").addEventListener("click", () => scrollToSection("minecraftSection"));
    document.getElementById("goToContinue").addEventListener("click", () => scrollToSection("continueSection"));
    document.getElementById("goToPlaylists").addEventListener("click", () => scrollToSection("playlistSection"));
    document.getElementById("goToYoutube").addEventListener("click", () => scrollToSection("youtubeSection"));
    document.getElementById("goToUploads").addEventListener("click", () => {
      scrollToSection("uploadsSection");
      uploadFilesInput.focus();
    });
    document.getElementById("goToChat").addEventListener("click", () => scrollToSection("chatSection"));
    document.getElementById("goToLibrary").addEventListener("click", () => scrollToSection("librarySection"));

    document.getElementById("heroOpenMinecraft").addEventListener("click", () => {
      scrollToSection("minecraftSection");
      minecraftUsernameInput.focus();
    });

    document.getElementById("heroRandomYoutube").addEventListener("click", () => {
      scrollToSection("youtubeSection");
      loadRandomYoutube();
    });

    document.getElementById("heroSearchYoutube").addEventListener("click", () => {
      scrollToSection("youtubeSection");
      ytSearchInput.focus();
    });

    [
      document.getElementById("libraryRandomButton"),
      document.getElementById("headerLibraryRandom"),
      document.getElementById("heroRandomLibrary")
    ].forEach(button => button.addEventListener("click", playRandomLibrary));

    document.getElementById("close").addEventListener("click", closePlayer);

    document.addEventListener("keydown", event => {
      if (event.key === "Escape" && isPlaying) {
        closePlayer();
      }
    });

    loadYoutubeIframeApi();
    setupDrawingCanvas();
    document.getElementById("feedbackSend")?.addEventListener("click", submitFeedback);
    document.getElementById("feedbackRefreshAdmin")?.addEventListener("click", loadFeedback);
    renderMinecraftPanel();
    fetchMovies();
    loadDrawings();
    loadFeedback();
    loadAccount();
    loadUploads();
    loadRandomYoutube();
    setInterval(fetchMovies, 3000);
    setInterval(loadChatData, 5000);
  </script>
</body>
</html>
"""

        html = html.replace("__MEDIA_FOLDER__", MOVIE_FOLDER)
        html = html.replace("<style>", f'<style nonce="{self._csp_nonce}">', 1)
        html = html.replace("<script>", f'<script nonce="{self._csp_nonce}">', 1)

        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.end_headers()
        self.safe_write(html.encode("utf-8"))

    def serve_logo(self):
        file_name = urllib.parse.unquote(self.path.replace("/logo/", ""))
        path = safe_media_path(file_name)
        if not path or not os.path.exists(path):
            self.send_error(404)
            return

        content_type = mimetypes.guess_type(path)[0] or "application/octet-stream"

        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.end_headers()

        with open(path, "rb") as handle:
            while chunk := handle.read(CHUNK_SIZE):
                self.safe_write(chunk)

    def stream_file(self, preview=False):
        prefix = "/preview/" if preview else "/movie/"
        file_name = urllib.parse.unquote(self.path.replace(prefix, ""))
        path = safe_media_path(file_name)

        if not path or not os.path.exists(path):
            self.send_error(404)
            return

        size = os.path.getsize(path)
        content_type = mimetypes.guess_type(path)[0] or "video/mp4"
        range_header = self.headers.get("Range")

        if range_header and range_header.startswith("bytes="):
            range_value = range_header.split("=", 1)[1]
            start_text, _, end_text = range_value.partition("-")

            try:
                start = int(start_text) if start_text else 0
                end = int(end_text) if end_text else size - 1
            except ValueError:
                self.send_error(416)
                return

            if start >= size or end >= size or start > end:
                self.send_error(416)
                return

            self.send_response(206)
            self.send_header("Content-Type", content_type)
            self.send_header("Accept-Ranges", "bytes")
            self.send_header("Content-Range", f"bytes {start}-{end}/{size}")
            self.send_header("Content-Length", str(end - start + 1))
            self.end_headers()

            with open(path, "rb") as handle:
                handle.seek(start)
                remaining = end - start + 1
                while remaining > 0:
                    chunk = handle.read(min(CHUNK_SIZE, remaining))
                    if not chunk:
                        break
                    self.safe_write(chunk)
                    remaining -= len(chunk)
            return

        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(size))
        self.send_header("Accept-Ranges", "bytes")
        self.end_headers()

        with open(path, "rb") as handle:
            while chunk := handle.read(CHUNK_SIZE):
                self.safe_write(chunk)


if __name__ == "__main__":
    migrate_legacy_storage_to_database()
    ensure_feedback_admin_account()

    # Render terminates HTTPS at its public edge. The Python app itself listens
    # on plain HTTP inside the Render service, which is the expected setup.
    server = ThreadingHTTPServer(("0.0.0.0", PORT), Handler)

    print(f"NotFlix server listening on 0.0.0.0:{PORT}")
    print("Public HTTPS is provided by Render. No local certificate is created.")

    server.serve_forever()
