from flask import Flask, render_template, render_template_string, request, redirect, url_for, session, flash, jsonify, send_file, send_from_directory
from openpyxl import Workbook, load_workbook
from werkzeug.security import generate_password_hash, check_password_hash
from functools import wraps
import os
from zipfile import BadZipFile
import shutil
import uuid
import json
import re
import time
from datetime import datetime
from pathlib import Path
import cv2
import mediapipe as mp
import numpy as np
import math
import base64
from collections import deque
import threading
import tempfile
import requests

# ============================================================
# RUNTIME ENVIRONMENT HELPERS (Render / local)
# ============================================================
# Render servers run in UTC, while teachers type exam windows in their own
# local time. Every "is this exam open?" decision therefore uses an explicit
# exam timezone (default India Standard Time) instead of the server clock.
from datetime import timedelta, timezone as _dt_timezone

EXAM_TIMEZONE_NAME = os.environ.get("EXAM_TIMEZONE", "Asia/Kolkata").strip() or "Asia/Kolkata"


def _exam_tzinfo():
    try:
        from zoneinfo import ZoneInfo
        return ZoneInfo(EXAM_TIMEZONE_NAME)
    except Exception:
        # tzdata missing (some slim images): fall back to a fixed IST offset.
        return _dt_timezone(timedelta(hours=5, minutes=30))


def _now_local():
    """Current wall-clock time in the exam timezone as a naive datetime."""
    return datetime.now(_exam_tzinfo()).replace(tzinfo=None)


ON_RENDER = (
    os.environ.get("RENDER", "").strip().lower() == "true"
    or bool(os.environ.get("RENDER_EXTERNAL_URL", "").strip())
)

try:
    import urllib3
    urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
except Exception:
    pass


def _ice_servers():
    """ICE servers for WebRTC. Add a TURN server via ICE_SERVERS_JSON for
    students/admins that sit behind strict college/corporate firewalls."""
    raw = os.environ.get("ICE_SERVERS_JSON", "").strip()
    if raw:
        try:
            parsed = json.loads(raw)
            if isinstance(parsed, list) and parsed:
                return parsed
        except Exception as exc:
            print("[ICE] ICE_SERVERS_JSON ignored:", exc)
    return [
        {"urls": "stun:stun.l.google.com:19302"},
        {"urls": "stun:stun1.l.google.com:19302"},
        {"urls": "stun:stun.cloudflare.com:3478"},
    ]

# ============================================================
# REMOTE ADMIN -> STUDENT WEBRTC VOICE SIGNALING
# ============================================================
# The audio is peer-to-peer WebRTC. These small in-memory records only
# carry the SDP offer/answer between the two browser clients.
VOICE_SIGNAL_TOKEN = os.environ.get(
    "VOICE_SIGNAL_TOKEN", "CHANGE_THIS_SHARED_VOICE_TOKEN"
)
VOICE_SIGNAL_TTL_SECONDS = 90
VOICE_SIGNAL_STATE = {}
VOICE_SIGNAL_LOCK = threading.Lock()

# Continuous browser-to-browser LIVE VIDEO signaling. Flask only exchanges
# SDP; the video itself travels over WebRTC directly between browsers.
VIDEO_SIGNAL_TTL_SECONDS = 30
VIDEO_SIGNAL_STATE = {}
VIDEO_SIGNAL_LOCK = threading.Lock()

# Teacher-controlled keyboard unlock password. Keep the real password only on
# the server (it is never embedded in the browser JavaScript). Change the
# default below or set KEYBOARD_UNLOCK_PASSWORD in the environment.
KEYBOARD_UNLOCK_PASSWORD = os.environ.get(
    "KEYBOARD_UNLOCK_PASSWORD", "ExamGuard@Unlock"
)

# Audio warning state: require sustained sound instead of a single noisy
# 2-second sample. This prevents tiny clicks / fan noise from becoming a
# warning.
# Conservative audio thresholds. Browser-side detection confirms sustained audio
# before sending a warning; this server endpoint is retained for compatibility.
AUDIO_THRESHOLD = 0.040
AUDIO_REQUIRED_CONSECUTIVE_SAMPLES = 4
AUDIO_HIGH_SAMPLE_COUNTS = {}
AUDIO_NOISE_FLOORS = {}
AUDIO_HIGH_SAMPLE_LOCK = threading.Lock()

RECORDING_ASSEMBLY_LOCKS = {}
RECORDING_ASSEMBLY_LOCK = threading.Lock()


app = Flask(__name__)
from flask import request, abort, render_template_string

@app.before_request
def block_mobile_devices():
    user_agent = request.headers.get("User-Agent", "").lower()

    mobile_signatures = (
        "android", "iphone", "ipad", "ipod",
        "mobile", "windows phone", "opera mini"
    )

    if any(signature in user_agent for signature in mobile_signatures):
        return render_template_string("""
            <!doctype html>
            <html>
            <head>
                <meta name="viewport" content="width=device-width, initial-scale=1">
                <title>Device Not Supported</title>
            </head>
            <body style="font-family:Arial;text-align:center;padding:40px">
                <h2>Device Not Supported</h2>
                <p>This examination can only be taken on a laptop or desktop computer.</p>
                <p>Please open the exam on a supported computer.</p>
            </body>
            </html>
        """), 403
app.secret_key = "student_exam_system_secret_key"

import socket

# Anchor every shared path to THIS FILE's own folder, not the current
# working directory. Relative paths depend on how Spyder/Python was
# launched, which can silently differ between two separate consoles
# running student_app.py and admin_app.py — causing them to read/write
# two different physical folders with no error, which looks exactly
# like "live monitoring does nothing." Absolute paths make both apps
# agree no matter how each one was started, as long as they're both
# in the same project folder.
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

DATABASE = os.path.join(BASE_DIR, "database.xlsx")
RECORDINGS_FOLDER = os.path.join(BASE_DIR, "recordings")
LIVE_FRAMES_FOLDER = os.path.join(BASE_DIR, "live_frames")

os.makedirs(RECORDINGS_FOLDER, exist_ok=True)
os.makedirs(os.path.join(RECORDINGS_FOLDER, ".examguard_parts"), exist_ok=True)
os.makedirs(LIVE_FRAMES_FOLDER, exist_ok=True)

# STUDENT -> ADMIN RESULT / RECORDING SYNC
ADMIN_URL_EXPLICIT = bool(os.environ.get("EXAMGUARD_ADMIN_BASE_URL", "").strip()) or ON_RENDER
ADMIN_SYNC_BASE_URL = (
    os.environ.get("EXAMGUARD_ADMIN_BASE_URL", "").strip().rstrip("/")
    or ("https://smart-exam-admin.onrender.com" if ON_RENDER else "https://192.168.1.24:5050")
)
ADMIN_SYNC_TOKEN=os.environ.get("EXAMGUARD_RECORDING_SYNC_TOKEN","EXAMGUARD-RECORDING-2026-LOCAL").strip()
ADMIN_SYNC_VERIFY_SSL = os.environ.get(
    "EXAMGUARD_ADMIN_VERIFY_SSL", "true" if ON_RENDER else "false"
).strip().lower() in ("1", "true", "yes", "on")
LIVE_MONITOR_BUILD="V3-DIRECT-PULL"
LIVE_SYNC_TOKEN=os.environ.get("EXAMGUARD_LIVE_SYNC_TOKEN","EXAMGUARD-LIVE-2026-LOCAL").strip()

def _student_public_signal_base_url():
    """Return the public URL admin must use to reach this student's signaling routes.

    Render sits behind a reverse proxy, so request.url_root may incorrectly
    report http:// even when the browser uses HTTPS. An explicit environment
    setting wins; otherwise honor forwarded headers and force HTTPS on Render.
    """
    configured = os.environ.get("STUDENT_PUBLIC_BASE_URL", "").strip().rstrip("/")
    if configured:
        return configured
    host = str(request.host or "").strip()
    if not host:
        return request.url_root.rstrip("/")
    forwarded_proto = str(request.headers.get("X-Forwarded-Proto", "")).split(",", 1)[0].strip().lower()
    is_render = os.environ.get("RENDER", "").strip().lower() == "true" or host.lower().endswith(".onrender.com")
    scheme = "https" if is_render else (forwarded_proto or request.scheme or "https")
    if scheme not in ("http", "https"):
        scheme = "https"
    return f"{scheme}://{host}"
ADMIN_SYNC_FOLDER=os.path.join(RECORDINGS_FOLDER,".examguard_admin_sync")
ADMIN_RESULT_SYNC_FOLDER=os.path.join(BASE_DIR,".examguard_admin_result_sync")
os.makedirs(ADMIN_SYNC_FOLDER,exist_ok=True)
os.makedirs(ADMIN_RESULT_SYNC_FOLDER,exist_ok=True)

# ============================================================
# ============================================================
# DATABASE FILE-SAFETY
# ============================================================
from zipfile import BadZipFile, ZipFile

DATABASE_LOCK = DATABASE + ".examguard.lock"
DATABASE_BACKUP = DATABASE + ".bak"
LOCK_STALE_SECONDS = 120.0


def _valid_xlsx(path):
    try:
        if not os.path.isfile(path) or os.path.getsize(path) < 100:
            return False
        with ZipFile(path, "r") as zf:
            names = set(zf.namelist())
            return "[Content_Types].xml" in names and "xl/workbook.xml" in names
    except (OSError, BadZipFile, EOFError, ValueError):
        return False


class _FileLock:
    def __init__(self, path):
        self.path = path
        self.fd = None

    def acquire(self, timeout=30.0):
        deadline = time.monotonic() + timeout
        while True:
            try:
                self.fd = os.open(self.path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
                os.write(self.fd, f"pid={os.getpid()}\ntime={time.time()}\n".encode("utf-8"))
                return
            except FileExistsError:
                try:
                    if time.time() - os.path.getmtime(self.path) > LOCK_STALE_SECONDS:
                        os.remove(self.path)
                        continue
                except (FileNotFoundError, OSError):
                    pass
                if time.monotonic() >= deadline:
                    raise TimeoutError("Timed out waiting for ExamGuard database lock")
                time.sleep(0.05)

    def release(self):
        if self.fd is not None:
            try:
                os.close(self.fd)
            finally:
                self.fd = None
        try:
            os.remove(self.path)
        except OSError:
            pass


def load_database(*args, **kwargs):
    shared = _shared_load_workbook(*args, **kwargs)
    if shared is not None:
        return shared
    last_error = None
    for attempt in range(10):
        try:
            if _valid_xlsx(DATABASE):
                return load_workbook(DATABASE, *args, **kwargs)
            last_error = BadZipFile("database.xlsx is not a valid XLSX archive")
        except (BadZipFile, EOFError, OSError) as exc:
            last_error = exc
        time.sleep(0.20 + 0.10 * attempt)
    if _valid_xlsx(DATABASE_BACKUP):
        shutil.copy2(DATABASE_BACKUP, DATABASE)
        return load_workbook(DATABASE, *args, **kwargs)
    raise last_error


def save_database(workbook):
    lock = _FileLock(DATABASE_LOCK)
    temp_path = None

    try:
        lock.acquire(30.0)

        fd, temp_path = tempfile.mkstemp(
            prefix="database_write_",
            suffix=".xlsx",
            dir=BASE_DIR
        )
        os.close(fd)

        workbook.save(temp_path)

        if not _valid_xlsx(temp_path):
            raise BadZipFile(
                "Temporary database write failed validation"
            )

        # Back up the existing local workbook.
        if _valid_xlsx(DATABASE):
            try:
                shutil.copy2(DATABASE, DATABASE_BACKUP)
            except OSError as exc:
                print("[DATABASE] Backup warning:", exc)

        # Persist to Neon before updating the local cache.
        if os.environ.get("DATABASE_URL", "").strip():
            with open(temp_path, "rb") as source:
                if not _shared_workbook_write(source.read()):
                    raise RuntimeError(
                        "Shared Neon workbook write failed"
                    )

        os.replace(temp_path, DATABASE)
        temp_path = None

        return True

    finally:
        if temp_path and os.path.exists(temp_path):
            try:
                os.remove(temp_path)
            except OSError:
                pass

        lock.release()

def _shared_workbook_connection():
    database_url = os.environ.get("DATABASE_URL", "").strip()
    if not database_url:
        return None
    import psycopg
    return psycopg.connect(database_url, connect_timeout=10)

def _shared_workbook_ensure_table(conn):
    with conn.cursor() as cur:
        cur.execute("""
            CREATE TABLE IF NOT EXISTS public.examguard_workbook_store (
                store_id INTEGER PRIMARY KEY CHECK (store_id = 1),
                workbook_bytes BYTEA NOT NULL,
                updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
            )
        """)

def _shared_workbook_bytes():
    conn = _shared_workbook_connection()
    if conn is None:
        return None
    try:
        with conn:
            _shared_workbook_ensure_table(conn)
            with conn.cursor() as cur:
                cur.execute("SELECT workbook_bytes FROM public.examguard_workbook_store WHERE store_id=1")
                row = cur.fetchone()
                return bytes(row[0]) if row and row[0] is not None else None
    finally:
        conn.close()

def _shared_workbook_write(data):
    conn = _shared_workbook_connection()
    if conn is None:
        return False
    try:
        with conn:
            _shared_workbook_ensure_table(conn)
            with conn.cursor() as cur:
                # Serialize writes across Admin and Student services.
                cur.execute("SELECT pg_advisory_xact_lock(741209, 1)")
                cur.execute("""
                    INSERT INTO public.examguard_workbook_store(store_id, workbook_bytes, updated_at)
                    VALUES (1, %s, NOW())
                    ON CONFLICT (store_id) DO UPDATE
                    SET workbook_bytes=EXCLUDED.workbook_bytes, updated_at=NOW()
                """, (data,))
        return True
    finally:
        conn.close()

def _shared_workbook_seed_if_empty():
    """Seed Neon once from the deployed workbook, without overwriting existing shared data."""
    if not os.environ.get("DATABASE_URL", "").strip():
        return
    conn = _shared_workbook_connection()
    if conn is None:
        return
    try:
        with conn:
            _shared_workbook_ensure_table(conn)
            with conn.cursor() as cur:
                cur.execute("SELECT 1 FROM public.examguard_workbook_store WHERE store_id=1")
                if cur.fetchone():
                    return
                if not _valid_xlsx(DATABASE):
                    print("[DATABASE] Shared workbook is empty and no valid local database.xlsx is available; import the workbook once.")
                    return
                from io import BytesIO
                buffer = BytesIO()
                with open(DATABASE, "rb") as source:
                    buffer.write(source.read())
                cur.execute("INSERT INTO public.examguard_workbook_store(store_id, workbook_bytes, updated_at) VALUES (1, %s, NOW()) ON CONFLICT (store_id) DO NOTHING", (buffer.getvalue(),))
                print("[DATABASE] Seeded shared Neon workbook from local database.xlsx.")
    finally:
        conn.close()

def _shared_load_workbook(*args, **kwargs):
    data = _shared_workbook_bytes()
    if data is None:
        _shared_workbook_seed_if_empty()
        data = _shared_workbook_bytes()
    if data is None:
        return None
    from io import BytesIO
    return load_workbook(BytesIO(data), *args, **kwargs)

def _shared_save_workbook(workbook):
    from io import BytesIO
    buffer = BytesIO()
    workbook.save(buffer)
    return _shared_workbook_write(buffer.getvalue())


# ============================================================
# EXAMGUARD SHARED STORE v2  (single source of truth)
# ------------------------------------------------------------
# Admin and Student services BOTH read and write the same workbook that
# lives in Neon (table public.examguard_workbook_store). Before this block the
# admin service used its own local database.xlsx, which is wiped on every
# Render restart and is never seen by the student service. That is why new
# exams never reached students, results never reached teachers, and delete
# reported "not authorized".
#
# Safety rules implemented here:
#   * Writes are serialised by a Postgres advisory lock.
#   * If somebody else saved after we loaded, our changes are re-applied on
#     top of the newest copy (row-level three-way merge) so two students
#     submitting at the same second never overwrite each other.
#   * A freshly created blank workbook can NEVER replace existing data.
#   * `exams_version` changes only when the Exams sheet changes; the student
#     dashboard polls it to refresh instantly.
# Without DATABASE_URL (local testing) the original file based behaviour is
# used unchanged.
# ============================================================
import io as _eg_io
from collections import Counter as _EgCounter

_eg_local_load_database = load_database
_eg_local_save_database = save_database

_EG_STORE_READY = False
_EG_STORE_READY_LOCK = threading.Lock()
_EG_VERSION_CACHE = {"t": 0.0, "v": 1}
_EG_BLOB_CACHE = {"t": 0.0, "data": None, "ver": 0}
_EG_BLOB_CACHE_LOCK = threading.Lock()
_EG_LOCAL_EXAMS_VERSION = {"v": int(time.time())}
_EG_MERGE_SHEETS_WITH_KEY = {"Results": "Result ID"}


def _eg_use_neon():
    return bool(os.environ.get("DATABASE_URL", "").strip())


def _eg_conn():
    import psycopg
    return psycopg.connect(os.environ["DATABASE_URL"].strip(), connect_timeout=10)


def _eg_ensure_store(conn):
    global _EG_STORE_READY
    if _EG_STORE_READY:
        return
    with _EG_STORE_READY_LOCK:
        if _EG_STORE_READY:
            return
        last = None
        for _ in range(3):
            try:
                with conn.cursor() as cur:
                    cur.execute("""
                        CREATE TABLE IF NOT EXISTS public.examguard_workbook_store (
                            store_id INTEGER PRIMARY KEY CHECK (store_id = 1),
                            workbook_bytes BYTEA NOT NULL,
                            updated_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
                        )""")
                    cur.execute("ALTER TABLE public.examguard_workbook_store "
                                "ADD COLUMN IF NOT EXISTS version BIGINT NOT NULL DEFAULT 1")
                    cur.execute("ALTER TABLE public.examguard_workbook_store "
                                "ADD COLUMN IF NOT EXISTS exams_version BIGINT NOT NULL DEFAULT 1")
                conn.commit()
                _EG_STORE_READY = True
                return
            except Exception as exc:       # two services creating it at once
                last = exc
                try:
                    conn.rollback()
                except Exception:
                    pass
                time.sleep(0.3)
        raise last


def _eg_norm_rows(ws):
    rows = []
    for r in ws.iter_rows(values_only=True):
        t = tuple(r)
        end = len(t)
        while end > 0 and t[end - 1] is None:
            end -= 1
        rows.append(t[:end])
    while rows and not rows[-1]:
        rows.pop()
    return rows


def _eg_fetch(conn):
    with conn.cursor() as cur:
        cur.execute("SELECT workbook_bytes, version FROM public.examguard_workbook_store WHERE store_id=1")
        row = cur.fetchone()
    if not row or row[0] is None:
        return None, 0
    return bytes(row[0]), int(row[1] or 1)


def _eg_seed_from_local(conn):
    """Seed Neon once from a local workbook (first ever deploy only)."""
    try:
        if _valid_xlsx(DATABASE):
            with open(DATABASE, "rb") as fh:
                data = fh.read()
            with conn.cursor() as cur:
                cur.execute("INSERT INTO public.examguard_workbook_store(store_id, workbook_bytes, version, exams_version) "
                            "VALUES (1, %s, 1, 1) ON CONFLICT (store_id) DO NOTHING", (data,))
            conn.commit()
            print("[STORE] Seeded shared workbook from local database.xlsx")
    except Exception as exc:
        print("[STORE] Seed skipped:", exc)
        try:
            conn.rollback()
        except Exception:
            pass


def _eg_get_blob(fresh=True):
    """Return (bytes, version) of the shared workbook."""
    if not fresh:
        with _EG_BLOB_CACHE_LOCK:
            if _EG_BLOB_CACHE["data"] is not None and time.time() - _EG_BLOB_CACHE["t"] < 1.5:
                return _EG_BLOB_CACHE["data"], _EG_BLOB_CACHE["ver"]
    last = None
    for attempt in range(4):
        conn = None
        try:
            conn = _eg_conn()
            _eg_ensure_store(conn)
            data, ver = _eg_fetch(conn)
            if data is None:
                _eg_seed_from_local(conn)
                data, ver = _eg_fetch(conn)
            if data is None:
                return None, 0
            with _EG_BLOB_CACHE_LOCK:
                _EG_BLOB_CACHE.update({"t": time.time(), "data": data, "ver": ver})
            return data, ver
        except Exception as exc:
            last = exc
            time.sleep(0.25 * (attempt + 1))
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
    raise RuntimeError(f"Shared database is unreachable: {last}")


def load_database(*args, **kwargs):
    if not _eg_use_neon():
        return _eg_local_load_database(*args, **kwargs)
    read_only = bool(kwargs.get("read_only"))
    data, ver = _eg_get_blob(fresh=not read_only)
    if data is None:
        # Brand new Neon database and no local file: create the blank schema once.
        try:
            initialize_database()
        except Exception as exc:
            print("[STORE] initialize_database failed:", exc)
        data, ver = _eg_get_blob(fresh=True)
        if data is None:
            raise RuntimeError("Shared workbook could not be created")
    wb = load_workbook(_eg_io.BytesIO(data), *args, **kwargs)
    if not read_only:
        wb._eg_base_version = ver
        wb._eg_base = {ws.title: _eg_norm_rows(ws) for ws in wb.worksheets}
    return wb


def _eg_merge_rows(name, base_rows, mine_rows, theirs_rows):
    """Re-apply my row additions/removals on top of the newest rows."""
    if base_rows == theirs_rows:
        return list(mine_rows)
    b_head = base_rows[0] if base_rows else ()
    m_head = mine_rows[0] if mine_rows else ()
    t_head = theirs_rows[0] if theirs_rows else ()
    if m_head != b_head:
        head = m_head if len(m_head) >= len(t_head) else t_head
    else:
        head = t_head or m_head
    base_body, mine_body, theirs_body = base_rows[1:], mine_rows[1:], theirs_rows[1:]
    added = _EgCounter(mine_body) - _EgCounter(base_body)
    removed = _EgCounter(base_body) - _EgCounter(mine_body)
    body = []
    for row in theirs_body:
        if removed.get(row, 0) > 0:
            removed[row] -= 1
            continue
        body.append(row)
    for row in mine_body:
        if added.get(row, 0) > 0:
            added[row] -= 1
            body.append(row)
    key_col = _EG_MERGE_SHEETS_WITH_KEY.get(name)
    if key_col and head and key_col in head:
        ki = head.index(key_col)
        rec_i = head.index("Recording File") if "Recording File" in head else None
        seen, out = {}, []
        for row in body:
            key = row[ki] if ki < len(row) else None
            if key in (None, ""):
                out.append(row)
                continue
            if key in seen:
                prev = out[seen[key]]
                if rec_i is not None and (len(row) <= rec_i or not row[rec_i]) and len(prev) > rec_i and prev[rec_i]:
                    row = tuple(list(row) + [None] * (rec_i + 1 - len(row)))
                    row = row[:rec_i] + (prev[rec_i],) + row[rec_i + 1:]
                out[seen[key]] = row
            else:
                seen[key] = len(out)
                out.append(row)
        body = out
    return [head] + body if (head or body) else []


def _eg_merge_bytes(changed, base, latest_bytes):
    latest = load_workbook(_eg_io.BytesIO(latest_bytes))
    for name, mine_rows in changed.items():
        if name in latest.sheetnames:
            ws = latest[name]
            theirs_rows = _eg_norm_rows(ws)
        else:
            ws = latest.create_sheet(name)
            theirs_rows = []
        merged = _eg_merge_rows(name, base.get(name, []), mine_rows, theirs_rows)
        if ws.max_row and ws.max_row > 0:
            ws.delete_rows(1, ws.max_row)
        for row in merged:
            ws.append(list(row))
    out = _eg_io.BytesIO()
    latest.save(out)
    latest.close()
    return out.getvalue()


def save_database(workbook):
    if not _eg_use_neon():
        return _eg_local_save_database(workbook)
    base = getattr(workbook, "_eg_base", None)
    base_ver = getattr(workbook, "_eg_base_version", None)
    changed = {}
    for ws in workbook.worksheets:
        rows = _eg_norm_rows(ws)
        if base is None or base.get(ws.title) != rows:
            changed[ws.title] = rows
    mine = _eg_io.BytesIO()
    workbook.save(mine)
    mine_bytes = mine.getvalue()
    exams_touched = int(("Exams" in changed) or ("ArchivedExams" in changed))
    last = None
    for attempt in range(4):
        conn = None
        try:
            conn = _eg_conn()
            _eg_ensure_store(conn)
            with conn.cursor() as cur:
                cur.execute("SELECT pg_advisory_xact_lock(741209, 1)")
                cur.execute("SELECT workbook_bytes, version FROM public.examguard_workbook_store "
                            "WHERE store_id=1 FOR UPDATE")
                row = cur.fetchone()
                if row is None or row[0] is None:
                    cur.execute("INSERT INTO public.examguard_workbook_store(store_id, workbook_bytes, version, exams_version) "
                                "VALUES (1, %s, 1, 1) ON CONFLICT (store_id) DO UPDATE SET "
                                "workbook_bytes=EXCLUDED.workbook_bytes, updated_at=NOW()", (mine_bytes,))
                else:
                    cur_ver = int(row[1] or 1)
                    if base is None:
                        # A workbook that was not loaded from the store (for
                        # example a blank one created at start-up) must never
                        # replace existing data.
                        conn.rollback()
                        print("[STORE] Ignored a blank-workbook save; shared data already exists")
                        return True
                    out_bytes = mine_bytes
                    if base_ver is not None and cur_ver != base_ver and changed:
                        out_bytes = _eg_merge_bytes(changed, base, bytes(row[0]))
                    elif not changed:
                        conn.rollback()
                        return True
                    cur.execute("UPDATE public.examguard_workbook_store SET workbook_bytes=%s, "
                                "version=version+1, exams_version=exams_version+%s, updated_at=NOW() "
                                "WHERE store_id=1", (out_bytes, exams_touched))
            conn.commit()
            with _EG_BLOB_CACHE_LOCK:
                _EG_BLOB_CACHE["data"] = None
            _EG_VERSION_CACHE["t"] = 0.0
            return True
        except Exception as exc:
            last = exc
            try:
                if conn is not None:
                    conn.rollback()
            except Exception:
                pass
            time.sleep(0.3 * (attempt + 1))
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
    raise RuntimeError(f"Shared database write failed: {last}")


def eg_exams_version():
    """Cheap counter that changes whenever the Exams sheet changes."""
    if not _eg_use_neon():
        return _EG_LOCAL_EXAMS_VERSION["v"]
    now = time.time()
    if now - _EG_VERSION_CACHE["t"] < 0.5:
        return _EG_VERSION_CACHE["v"]
    conn = None
    try:
        conn = _eg_conn()
        _eg_ensure_store(conn)
        with conn.cursor() as cur:
            cur.execute("SELECT exams_version FROM public.examguard_workbook_store WHERE store_id=1")
            row = cur.fetchone()
        if row:
            _EG_VERSION_CACHE["v"] = int(row[0] or 1)
        _EG_VERSION_CACHE["t"] = now
    except Exception as exc:
        print("[STORE] exams_version read failed:", exc)
    finally:
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass
    return _EG_VERSION_CACHE["v"]


# =========================================================
# MEDIAPIPE FACE MONITORING SETUP
# =========================================================

mp_face_mesh = mp.solutions.face_mesh

LEFT_EYE = [33, 160, 158, 133, 153, 144]
RIGHT_EYE = [362, 385, 387, 263, 373, 380]
MOUTH = [61, 291, 13, 14]
NOSE = 1
CHIN = 152
LEFT_CHEEK = 234
RIGHT_CHEEK = 454

# Iris center landmarks — only available because FaceMesh is
# initialized with refine_landmarks=True. These track where the
# pupil is actually pointing, independent of head rotation, which
# is what "eye movement" / gaze tracking actually needs.
LEFT_IRIS_CENTER = 468
RIGHT_IRIS_CENTER = 473

# Upper/lower eyelid landmarks, used for VERTICAL gaze (up/down),
# separate from the eye corner landmarks used for horizontal gaze.
LEFT_EYE_TOP = [160, 158]
LEFT_EYE_BOTTOM = [153, 144]
RIGHT_EYE_TOP = [385, 387]
RIGHT_EYE_BOTTOM = [373, 380]

EAR_THRESHOLD = 0.20
# Inner-lip opening ratio. Talking/yawning pushes this well above a closed
# mouth (~0.02). It must stay above the threshold on several recent frames.
MAR_THRESHOLD = 0.28

# ---- Head pose: DEVIATION (degrees) from the student's own calm baseline ----
# The first few good frames after the exam starts are used to learn how this
# particular student sits in front of this particular camera. Warnings are then
# based on how far the head moves away from that baseline.
YAW_THRESHOLD = float(os.environ.get("AI_YAW_THRESHOLD", "20"))
PITCH_THRESHOLD = float(os.environ.get("AI_PITCH_THRESHOLD", "18"))
ROLL_THRESHOLD = float(os.environ.get("AI_ROLL_THRESHOLD", "18"))

# ---- Eye gaze: DEVIATION of the iris ratio from the student's own baseline ----
GAZE_THRESHOLD_H = float(os.environ.get("AI_GAZE_H", "0.11"))
GAZE_THRESHOLD_V = float(os.environ.get("AI_GAZE_V", "0.13"))

CALIBRATION_FRAMES = 5

# ---- Debounce windows. "N of last M" frames (1 frame ~ 1 second) ----
FRAME_CHECK = 4                     # eyes closed: 4 consecutive frames
NO_FACE_FRAME_CHECK = 4             # no face at all: 4 consecutive frames
HEAD_POSE_NEED, HEAD_POSE_WINDOW = 3, 4
GAZE_NEED, GAZE_WINDOW = 3, 4
MOUTH_NEED, MOUTH_WINDOW = 3, 4
MULTI_NEED, MULTI_WINDOW = 2, 3
PHONE_NEED, PHONE_WINDOW = 2, 4
# Lighting: mean brightness (0-255) of the camera frame. Below the limit for
# 3 of the last 4 frames the student gets a "room too dark" warning.
DIM_MEAN_THRESHOLD = float(os.environ.get("AI_DIM_MEAN", "55"))
DIM_NEED, DIM_WINDOW = 3, 4
# No face anywhere in the frame for this many seconds ends the exam.
NO_FACE_END_SECONDS = float(os.environ.get("AI_NO_FACE_END_SECONDS", "20"))
# If the calm baseline could not be learnt normally, learn it from whatever
# single-face frames were seen after this many frames (never stay uncalibrated).
CALIBRATION_FALLBACK_FRAMES = 12
ANALYSIS_MAX_WIDTH = 480
# Kept for backwards compatibility with older code paths.
GAZE_FRAME_CHECK = GAZE_NEED
HEAD_POSE_FRAME_CHECK = HEAD_POSE_NEED
MULTIPLE_FACE_FRAME_CHECK = MULTI_NEED
PHONE_FRAME_CHECK = PHONE_NEED

# A face smaller than this fraction of the frame width is treated as a poster /
# far background object, not a second person sitting next to the student.
FACE_MIN_REL_WIDTH = float(os.environ.get("AI_FACE_MIN_REL_WIDTH", "0.07"))

_DEFAULT_LATEST_STATS = {
    "ear": 0, "mar": 0, "closure": 0, "blink_rate": 0,
    "yaw": 0, "pitch": 0, "roll": 0, "face_count": 0,
    "status": "No Face", "eyes": "Unknown", "mouth": "Normal",
    "looking": "Unknown", "head_pose": "Unknown", "eye_gaze": "Unknown", "gaze_ratio": 0.5,
    "warning": False, "warning_message": ""
}

# =========================================================
# PER-STUDENT MONITORING STATE
# =========================================================
# FIX: everything here (ear_history, blink_count, total_frames,
# eye_closed_frames, gaze_off_frames, mouth_open_frames,
# last_blink_time, latest_stats — and, worse, the single shared
# `face_mesh` MediaPipe object itself) used to be ONE set of plain
# module-level globals. Every student's /student/exam/monitor
# request read and wrote the exact same variables, so with more
# than one student active at once:
#   - one student's blink/eye/gaze counters leaked into another
#     student's warnings ("false warnings" for one student caused
#     by a completely different student's face), and
#   - MediaPipe's FaceMesh is explicitly not thread-safe and also
#     keeps internal frame-to-frame TRACKING state (static_image_
#     mode=False) — feeding it alternating frames from different
#     students' faces corrupts that tracking state and can throw,
#     hang, or silently return garbage landmarks. This alone is
#     enough to make "live monitoring" appear to stop working the
#     moment a second student starts an exam.
#
# Fix: each (student, exam) attempt gets its OWN isolated state,
# including its own FaceMesh instance, stored in this registry and
# guarded by its own lock. States are released as soon as an exam
# is submitted, and a background sweep also reclaims anything left
# behind by a student who closed their browser mid-exam, so the
# registry (and the MediaPipe/OpenCV resources each entry holds)
# never grows without bound over a long-running server.
MONITOR_STATE_REGISTRY = {}
MONITOR_STATE_REGISTRY_LOCK = threading.Lock()
MONITOR_STATE_MAX_IDLE_SECONDS = 20 * 60  # reclaim after 20 min of no frames
MONITOR_STATE_SWEEP_INTERVAL_SECONDS = 5 * 60
_MONITOR_SWEEP_STARTED = False
_MONITOR_SWEEP_LOCK = threading.Lock()


def _new_monitor_state():
    return {
        "lock": threading.Lock(),
        "face_mesh": mp_face_mesh.FaceMesh(
            static_image_mode=False,
            max_num_faces=3,
            refine_landmarks=True,
            min_detection_confidence=0.5,
            min_tracking_confidence=0.5,
        ),
        "ear_history": deque(maxlen=20),
        "blink_times": deque(maxlen=20),
        "blink_count": 0,
        "total_frames": 0,
        "eye_closed_frames": 0,
        "no_face_frames": 0,
        "last_blink_time": 0.0,
        # sliding "N of last M" windows
        "yaw_hist": deque(maxlen=HEAD_POSE_WINDOW),
        "pitch_hist": deque(maxlen=HEAD_POSE_WINDOW),
        "roll_hist": deque(maxlen=HEAD_POSE_WINDOW),
        "turned_hist": deque(maxlen=HEAD_POSE_WINDOW),
        "gaze_hist": deque(maxlen=GAZE_WINDOW),
        "mouth_hist": deque(maxlen=MOUTH_WINDOW),
        "multi_hist": deque(maxlen=MULTI_WINDOW),
        "phone_hist": deque(maxlen=PHONE_WINDOW),
        "dim_hist": deque(maxlen=DIM_WINDOW),
        "no_face_since": None,
        "frame_no": 0,
        "last_phone_found": False,
        # per-student calm baseline (head pose + gaze)
        "calib": {"yaw": [], "pitch": [], "roll": [], "gh": [], "gv": []},
        "calib_any": {"yaw": [], "pitch": [], "roll": [], "gh": [], "gv": []},
        "baseline": None,
        "last_phone_score": 0.0,
        "latest_stats": dict(_DEFAULT_LATEST_STATS),
        "last_seen": time.time(),
    }


def _monitor_key(student_id, exam_id):
    return f"{student_id}:{exam_id}"


def _get_monitor_state(key):
    with MONITOR_STATE_REGISTRY_LOCK:
        st = MONITOR_STATE_REGISTRY.get(key)
        if st is None:
            st = _new_monitor_state()
            MONITOR_STATE_REGISTRY[key] = st
        st["last_seen"] = time.time()
        return st


def _release_monitor_state(key):
    with MONITOR_STATE_REGISTRY_LOCK:
        st = MONITOR_STATE_REGISTRY.pop(key, None)
    if st is not None:
        try:
            st["face_mesh"].close()
        except Exception:
            pass


def _sweep_idle_monitor_states():
    while True:
        time.sleep(MONITOR_STATE_SWEEP_INTERVAL_SECONDS)
        now = time.time()
        stale = []
        with MONITOR_STATE_REGISTRY_LOCK:
            for key, st in list(MONITOR_STATE_REGISTRY.items()):
                if now - st.get("last_seen", 0) > MONITOR_STATE_MAX_IDLE_SECONDS:
                    stale.append((key, st))
            for key, _st in stale:
                MONITOR_STATE_REGISTRY.pop(key, None)
        for _key, st in stale:
            try:
                st["face_mesh"].close()
            except Exception:
                pass
        if stale:
            print(f"[MONITOR] Reclaimed {len(stale)} idle monitoring session(s)")


def _start_monitor_sweep():
    global _MONITOR_SWEEP_STARTED
    with _MONITOR_SWEEP_LOCK:
        if not _MONITOR_SWEEP_STARTED:
            threading.Thread(target=_sweep_idle_monitor_states, daemon=True, name="monitor-state-sweep").start()
            _MONITOR_SWEEP_STARTED = True


_start_monitor_sweep()




def calculate_ear(landmarks, eye_indices, width, height):

    points = []

    for index in eye_indices:

        x = int(landmarks[index].x * width)
        y = int(landmarks[index].y * height)

        points.append(np.array([x, y]))


    p1, p2, p3, p4, p5, p6 = points


    vertical_1 = np.linalg.norm(p2 - p6)

    vertical_2 = np.linalg.norm(p3 - p5)

    horizontal = np.linalg.norm(p1 - p4)


    if horizontal == 0:
        return 0


    ear = (
        vertical_1 + vertical_2
    ) / (
        2.0 * horizontal
    )


    return float(ear)



def calculate_mar(landmarks, width, height):

    left = landmarks[61]

    right = landmarks[291]

    top = landmarks[13]

    bottom = landmarks[14]


    left_point = np.array([
        left.x * width,
        left.y * height
    ])

    right_point = np.array([
        right.x * width,
        right.y * height
    ])

    top_point = np.array([
        top.x * width,
        top.y * height
    ])

    bottom_point = np.array([
        bottom.x * width,
        bottom.y * height
    ])


    vertical = np.linalg.norm(
        top_point - bottom_point
    )

    horizontal = np.linalg.norm(
        left_point - right_point
    )


    if horizontal == 0:
        return 0


    mar = vertical / horizontal

    return float(mar)


def calculate_gaze_ratio(landmarks, eye_corner_indices, iris_center_index, width):
    """
    Returns a 0.0–1.0 value describing where the iris sits horizontally
    between the eye's two corners: 0.0 = fully toward one corner (eye
    looking hard left), 1.0 = fully toward the other corner (looking
    hard right), ~0.5 = centered. This is INDEPENDENT of head rotation
    — a student can hold their head still and still be caught looking
    sideways at another screen/paper using this.
    """

    corner_1 = landmarks[eye_corner_indices[0]]
    corner_2 = landmarks[eye_corner_indices[1]]
    iris = landmarks[iris_center_index]

    corner_1_x = corner_1.x * width
    corner_2_x = corner_2.x * width
    iris_x = iris.x * width

    eye_width = corner_2_x - corner_1_x

    if eye_width == 0:
        return 0.5

    ratio = (iris_x - corner_1_x) / eye_width

    return float(max(0.0, min(1.0, ratio)))


def calculate_vertical_gaze_ratio(landmarks, top_indices, bottom_indices, iris_center_index, height):
    """
    Same idea as calculate_gaze_ratio but for the vertical axis:
    0.0 = iris pushed up toward the top eyelid (looking UP),
    1.0 = iris pushed down toward the bottom eyelid (looking DOWN),
    ~0.5 = centered. Needed separately from horizontal gaze because
    "moving eyes up/down/left/right" requires both axes, not just
    left-right.
    """

    top_y = sum(landmarks[i].y for i in top_indices) / len(top_indices) * height
    bottom_y = sum(landmarks[i].y for i in bottom_indices) / len(bottom_indices) * height
    iris_y = landmarks[iris_center_index].y * height

    eye_height = bottom_y - top_y

    if eye_height == 0:
        return 0.5

    ratio = (iris_y - top_y) / eye_height

    return float(max(0.0, min(1.0, ratio)))



def calculate_head_pose(
    landmarks,
    width,
    height
):

    # =====================================================
    # 2D FACE POINTS
    # =====================================================

    image_points = np.array([

        # Nose
        [
            landmarks[1].x * width,
            landmarks[1].y * height
        ],

        # Chin
        [
            landmarks[152].x * width,
            landmarks[152].y * height
        ],

        # Left eye
        [
            landmarks[33].x * width,
            landmarks[33].y * height
        ],

        # Right eye
        [
            landmarks[263].x * width,
            landmarks[263].y * height
        ],

        # Left mouth
        [
            landmarks[61].x * width,
            landmarks[61].y * height
        ],

        # Right mouth
        [
            landmarks[291].x * width,
            landmarks[291].y * height
        ]

    ],
    dtype=np.float64)


    # =====================================================
    # 3D FACE MODEL
    # =====================================================

    model_points = np.array([

        [0.0, 0.0, 0.0],

        [0.0, -63.6, -12.5],

        [-43.3, 32.7, -26.0],

        [43.3, 32.7, -26.0],

        [-28.9, -28.9, -24.1],

        [28.9, -28.9, -24.1]

    ],
    dtype=np.float64)


    # =====================================================
    # CAMERA MATRIX
    # =====================================================

    focal_length = width

    center = (
        width / 2,
        height / 2
    )


    camera_matrix = np.array([

        [
            focal_length,
            0,
            center[0]
        ],

        [
            0,
            focal_length,
            center[1]
        ],

        [
            0,
            0,
            1
        ]

    ],
    dtype=np.float64)


    distortion = np.zeros(
        (4, 1)
    )


    # =====================================================
    # SOLVE PNP
    # =====================================================

    success, rotation_vector, translation_vector = cv2.solvePnP(

        model_points,

        image_points,

        camera_matrix,

        distortion,

        flags=cv2.SOLVEPNP_ITERATIVE

    )


    if not success:

        return 0.0, 0.0, 0.0


    # =====================================================
    # ROTATION MATRIX
    # =====================================================

    rotation_matrix, _ = cv2.Rodrigues(
        rotation_vector
    )


    # =====================================================
    # DECOMPOSE ROTATION
    # =====================================================

    angles = cv2.RQDecomp3x3(
        rotation_matrix
    )


    # OpenCV returns:
    # angles[0] = (pitch, yaw, roll)

    pitch = float(angles[0][0])

    yaw = float(angles[0][1])

    roll = float(angles[0][2])


    # =====================================================
    # NORMALIZE ANGLES
    # =====================================================

    # Convert values like 170 degrees
    # into approximately -10 degrees.

    if pitch > 90:

        pitch = pitch - 180

    elif pitch < -90:

        pitch = pitch + 180


    if yaw > 90:

        yaw = yaw - 180

    elif yaw < -90:

        yaw = yaw + 180


    if roll > 90:

        roll = roll - 180

    elif roll < -90:

        roll = roll + 180


    return (

        pitch,

        yaw,

        roll

    )




PHONE_DETECTION_AVAILABLE = False
_object_detector = None
_PHONE_DETECTOR_LOCK = threading.Lock()

# efficientdet_lite0 reports a phone held toward a webcam with scores that are
# frequently 0.30-0.55. The old 0.35 threshold combined with a "must be seen in
# consecutive frames" counter that was reset by every skipped frame meant a
# phone could never be confirmed. Now: every frame is checked, a low per-frame
# threshold is used, and the confirmation is "2 hits in the last 4 frames".
PHONE_SCORE_THRESHOLD = float(os.environ.get("PHONE_SCORE_THRESHOLD", "0.30"))
PHONE_LABELS = {"cell phone", "mobile phone", "phone", "cellphone", "smartphone"}
OBJECT_MODEL_URL = (
    "https://storage.googleapis.com/mediapipe-models/object_detector/"
    "efficientdet_lite0/float32/1/efficientdet_lite0.tflite"
)


def _find_or_download_object_model():
    for folder in (BASE_DIR, os.getcwd()):
        candidate = str(Path(folder, "efficientdet_lite0.tflite").resolve())
        if os.path.isfile(candidate) and os.path.getsize(candidate) > 1_000_000:
            return candidate
    target = str(Path(BASE_DIR, "efficientdet_lite0.tflite").resolve())
    try:
        print("Mobile phone model not found; downloading efficientdet_lite0.tflite ...")
        r = requests.get(OBJECT_MODEL_URL, timeout=60)
        if r.ok and len(r.content) > 1_000_000:
            with open(target, "wb") as fh:
                fh.write(r.content)
            return target
    except Exception as exc:
        print("Model download failed:", exc)
    return ""


def _init_phone_detector():
    global PHONE_DETECTION_AVAILABLE, _object_detector
    try:
        from mediapipe.tasks.python import vision as _mp_vision
        from mediapipe.tasks.python.core.base_options import BaseOptions as _MPBaseOptions

        model_path = _find_or_download_object_model()
        if not model_path:
            print("Mobile phone detection: DISABLED - efficientdet_lite0.tflite not found "
                  "next to this script. Everything else runs normally.")
            return
        common = dict(
            base_options=_MPBaseOptions(model_asset_path=model_path.replace("\\", "/")),
            running_mode=_mp_vision.RunningMode.IMAGE,
            score_threshold=PHONE_SCORE_THRESHOLD,
            max_results=10,
        )
        try:
            options = _mp_vision.ObjectDetectorOptions(category_allowlist=["cell phone"], **common)
        except TypeError:
            options = _mp_vision.ObjectDetectorOptions(**common)
        _object_detector = _mp_vision.ObjectDetector.create_from_options(options)
        PHONE_DETECTION_AVAILABLE = True
        print("Mobile phone detection: ENABLED (", model_path, ")")
    except Exception as exc:
        print("Mobile phone detection: DISABLED - setup error:", exc,
              "| Everything else runs normally without this feature.")


_init_phone_detector()


def detect_phone_in_frame(frame):
    """Return (found, best_score) for a cell phone anywhere in the frame."""
    if not PHONE_DETECTION_AVAILABLE or _object_detector is None:
        return False, 0.0
    try:
        rgb = np.ascontiguousarray(cv2.cvtColor(frame, cv2.COLOR_BGR2RGB))
        image = mp.Image(image_format=mp.ImageFormat.SRGB, data=rgb)
        with _PHONE_DETECTOR_LOCK:
            result = _object_detector.detect(image)
        best = 0.0
        for detection in result.detections:
            for category in detection.categories:
                name = (category.category_name or "").strip().lower()
                if name in PHONE_LABELS:
                    best = max(best, float(category.score or 0.0))
        return best >= PHONE_SCORE_THRESHOLD, best
    except Exception as exc:
        print("Phone detection frame error (ignored):", exc)
        return False, 0.0


# A dedicated full-range face detector is far better than FaceMesh at noticing a
# second (smaller / further away / partly turned) person in the frame.
_FACE_DETECTOR = None
_FACE_DETECTOR_LOCK = threading.Lock()
try:
    _FACE_DETECTOR = mp.solutions.face_detection.FaceDetection(
        model_selection=1, min_detection_confidence=0.55
    )
except Exception as _fd_exc:
    print("Face detector unavailable (multiple-face check uses FaceMesh only):", _fd_exc)


def count_faces_detector(rgb):
    if _FACE_DETECTOR is None:
        return 0
    try:
        with _FACE_DETECTOR_LOCK:
            res = _FACE_DETECTOR.process(rgb)
        n = 0
        for det in (res.detections or []):
            box = det.location_data.relative_bounding_box
            if box.width >= FACE_MIN_REL_WIDTH:
                n += 1
        return n
    except Exception as exc:
        print("Face detector frame error (ignored):", exc)
        return 0


def _hist_confirm(hist, value, need):
    hist.append(bool(value))
    return sum(1 for item in hist if item) >= need


def _median(values):
    ordered = sorted(values)
    return ordered[len(ordered) // 2] if ordered else 0.0


def _face_area(landmarks):
    xs = [p.x for p in landmarks]
    ys = [p.y for p in landmarks]
    return (max(xs) - min(xs)) * (max(ys) - min(ys))


def _blank_stats(face_count, status, warnings):
    top = warnings[0] if warnings else None
    return {
        "ear": 0, "mar": 0, "closure": 0, "blink_rate": 0, "blink_count": 0,
        "yaw": 0, "pitch": 0, "roll": 0, "face_count": face_count,
        "status": status, "eyes": "Unknown", "mouth": "Unknown",
        "looking": "Unknown", "head_pose": "Unknown", "eye_gaze": "Unknown",
        "gaze_ratio": 0.5,
        "warning": bool(warnings),
        "warning_message": top[1] if top else "",
        "warning_type": top[0] if top else "",
        "warnings": [{"type": t, "message": m} for t, m in warnings],
    }


def analyze_face_frame(frame, monitor_key):
    """Analyse one webcam frame for one student.

    Returns a stats dict. `warnings` is the list of independent malpractice
    EVENTS active right now (phone, other person, no face, plus at most ONE
    attention warning such as head turned / eyes away / mouth open), so one
    physical action never costs several strikes at once.
    """
    state = _get_monitor_state(monitor_key)

    with state["lock"]:
        height, width = frame.shape[:2]
        if width > ANALYSIS_MAX_WIDTH:
            scale = ANALYSIS_MAX_WIDTH / float(width)
            frame = cv2.resize(frame, (ANALYSIS_MAX_WIDTH, max(1, int(height * scale))),
                               interpolation=cv2.INTER_AREA)
            height, width = frame.shape[:2]
        rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)

        # Lighting check (cheap): average brightness of the whole frame.
        brightness = float(cv2.mean(cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY))[0])
        dim_confirmed = _hist_confirm(state["dim_hist"], brightness < DIM_MEAN_THRESHOLD, DIM_NEED)

        results = state["face_mesh"].process(rgb)
        state["total_frames"] += 1
        state["frame_no"] += 1

        mesh_faces = list(results.multi_face_landmarks or [])
        mesh_count = len(mesh_faces)
        detector_count = count_faces_detector(rgb)
        face_count = max(mesh_count, detector_count)

        # The phone model is the heaviest step: run it on every second frame
        # and reuse the answer in between (a phone stays in view for seconds).
        if state["frame_no"] % 2 == 1:
            phone_found, phone_score = detect_phone_in_frame(frame)
            state["last_phone_found"] = phone_found
            state["last_phone_score"] = phone_score
        else:
            phone_found, phone_score = state["last_phone_found"], state["last_phone_score"]
        phone_confirmed = _hist_confirm(state["phone_hist"], phone_found, PHONE_NEED)
        multi_confirmed = _hist_confirm(state["multi_hist"], face_count >= 2, MULTI_NEED)

        # How long has NOBODY been in front of the camera?
        now_ts = time.time()
        if mesh_count == 0 and detector_count == 0:
            if state["no_face_since"] is None:
                state["no_face_since"] = now_ts
            absent_seconds = now_ts - state["no_face_since"]
        else:
            state["no_face_since"] = None
            absent_seconds = 0.0
        must_terminate = absent_seconds >= NO_FACE_END_SECONDS

        events = []
        if dim_confirmed:
            events.append(("lighting_warning",
                           "The room is too dark. Please turn on a light so your face is clearly visible."))
        if phone_confirmed:
            events.append(("phone_warning", "Mobile phone detected. Please remove it."))
        if multi_confirmed:
            events.append(("multiple_face_warning",
                           "Other person detected. Only the student should be visible."))

        # ---------------------------------------------------------------
        # No FaceMesh face at all
        # ---------------------------------------------------------------
        if mesh_count == 0:
            if detector_count >= 1:
                # A face is there but too turned/tilted for FaceMesh to lock
                # on: that is a head-direction problem, not a missing student.
                state["no_face_frames"] = 0
                turned = _hist_confirm(state["turned_hist"], True, HEAD_POSE_NEED)
                if turned and not events:
                    events.append(("head_direction_warning",
                                   "Please look straight at the camera."))
                stats = _blank_stats(face_count, "Warning" if events else "Normal", events)
                stats["looking"] = "Turned away"
            else:
                state["turned_hist"].append(False)
                state["no_face_frames"] += 1
                if state["no_face_frames"] >= NO_FACE_FRAME_CHECK and not dim_confirmed:
                    left = max(0, int(NO_FACE_END_SECONDS - absent_seconds))
                    events.append(("no_face_warning",
                                   f"Face not detected. Please look at the camera. "
                                   f"The exam ends automatically in {left} s if you do not return."))
                stats = _blank_stats(0, "No Face" if not events else "Warning", events)
            stats["phone_score"] = round(phone_score, 3)
            stats["brightness"] = round(brightness, 1)
            stats["no_face_seconds"] = round(absent_seconds, 1)
            if must_terminate:
                stats["terminate"] = True
                stats["terminate_reason"] = "no_face_timeout"
                stats["warning"] = True
                stats["warning_message"] = "Your face was not visible for too long. The exam is being ended."
            stats["calibrated"] = state["baseline"] is not None
            state["latest_stats"] = stats
            return stats

        state["no_face_frames"] = 0
        state["turned_hist"].append(False)

        # ---------------------------------------------------------------
        # Primary face = the largest one (the student sitting at the camera)
        # ---------------------------------------------------------------
        primary = max(mesh_faces, key=lambda f: _face_area(f.landmark))
        face_landmarks = primary.landmark

        left_ear = calculate_ear(face_landmarks, LEFT_EYE, width, height)
        right_ear = calculate_ear(face_landmarks, RIGHT_EYE, width, height)
        ear = (left_ear + right_ear) / 2.0
        state["ear_history"].append(ear)

        eyes_closed = ear < EAR_THRESHOLD
        if eyes_closed:
            state["eye_closed_frames"] += 1
            eyes_status = "Closed"
        else:
            state["eye_closed_frames"] = 0
            eyes_status = "Open"

        ear_history = state["ear_history"]
        if len(ear_history) >= 2:
            if ear_history[-2] < EAR_THRESHOLD and ear >= EAR_THRESHOLD:
                current_time = time.time()
                if current_time - state["last_blink_time"] > 0.15:
                    state["blink_count"] += 1
                    state["blink_times"].append(current_time)
                    state["last_blink_time"] = current_time

        current_time = time.time()
        blink_times = state["blink_times"]
        while blink_times and current_time - blink_times[0] > 60:
            blink_times.popleft()
        blink_rate = len(blink_times)

        closure_percentage = (
            state["eye_closed_frames"] / state["total_frames"] * 100
            if state["total_frames"] > 0 else 0
        )

        mar = calculate_mar(face_landmarks, width, height)
        mouth_open_now = mar > MAR_THRESHOLD
        mouth_status = "Open" if mouth_open_now else "Normal"
        mouth_confirmed = _hist_confirm(state["mouth_hist"], mouth_open_now, MOUTH_NEED)

        # Eye gaze (iris position inside the eye), both axes.
        gaze_h = (
            calculate_gaze_ratio(face_landmarks, (LEFT_EYE[0], LEFT_EYE[3]), LEFT_IRIS_CENTER, width)
            + calculate_gaze_ratio(face_landmarks, (RIGHT_EYE[0], RIGHT_EYE[3]), RIGHT_IRIS_CENTER, width)
        ) / 2.0
        gaze_v = (
            calculate_vertical_gaze_ratio(face_landmarks, LEFT_EYE_TOP, LEFT_EYE_BOTTOM, LEFT_IRIS_CENTER, height)
            + calculate_vertical_gaze_ratio(face_landmarks, RIGHT_EYE_TOP, RIGHT_EYE_BOTTOM, RIGHT_IRIS_CENTER, height)
        ) / 2.0
        gaze_ratio = (gaze_h + gaze_v) / 2.0

        pitch, yaw, roll = calculate_head_pose(face_landmarks, width, height)

        # ---------------------------------------------------------------
        # Per-student baseline (calm, facing the screen)
        # ---------------------------------------------------------------
        baseline = state["baseline"]
        if baseline is None and mesh_count == 1 and not eyes_closed:
            any_c = state["calib_any"]
            for key, val in (("yaw", yaw), ("pitch", pitch), ("roll", roll), ("gh", gaze_h), ("gv", gaze_v)):
                any_c[key].append(val)
                del any_c[key][:-40]
            if state["total_frames"] >= CALIBRATION_FALLBACK_FRAMES and len(any_c["yaw"]) >= 8:
                state["baseline"] = baseline = {k: _median(any_c[k]) for k in ("yaw", "pitch", "roll", "gh", "gv")}
        if baseline is None:
            calm = (
                mesh_count == 1 and not eyes_closed
                and abs(yaw) < 30 and abs(pitch) < 35 and abs(roll) < 30
            )
            if calm:
                calib = state["calib"]
                calib["yaw"].append(yaw)
                calib["pitch"].append(pitch)
                calib["roll"].append(roll)
                calib["gh"].append(gaze_h)
                calib["gv"].append(gaze_v)
                if len(calib["yaw"]) >= CALIBRATION_FRAMES:
                    state["baseline"] = baseline = {
                        "yaw": _median(calib["yaw"]),
                        "pitch": _median(calib["pitch"]),
                        "roll": _median(calib["roll"]),
                        "gh": _median(calib["gh"]),
                        "gv": _median(calib["gv"]),
                    }
        calibrated = baseline is not None
        base = baseline or {"yaw": 0.0, "pitch": 0.0, "roll": 0.0, "gh": 0.5, "gv": 0.5}

        d_yaw = yaw - base["yaw"]
        d_pitch = pitch - base["pitch"]
        d_roll = roll - base["roll"]
        d_gh = gaze_h - base["gh"]
        d_gv = gaze_v - base["gv"]

        if d_yaw >= YAW_THRESHOLD:
            looking = "Looking Right"
        elif d_yaw <= -YAW_THRESHOLD:
            looking = "Looking Left"
        else:
            looking = "Looking Center"

        if abs(d_roll) >= ROLL_THRESHOLD:
            head_pose = "Head Tilted"
        elif d_pitch >= PITCH_THRESHOLD:
            head_pose = "Looking Down"
        elif d_pitch <= -PITCH_THRESHOLD:
            head_pose = "Looking Up"
        else:
            head_pose = "Normal"

        horizontal_label = "Left" if d_gh < -GAZE_THRESHOLD_H else ("Right" if d_gh > GAZE_THRESHOLD_H else None)
        vertical_label = "Up" if d_gv < -GAZE_THRESHOLD_V else ("Down" if d_gv > GAZE_THRESHOLD_V else None)
        if vertical_label and horizontal_label:
            eye_gaze = f"Eyes {vertical_label}-{horizontal_label}"
        elif vertical_label:
            eye_gaze = f"Eyes {vertical_label}"
        elif horizontal_label:
            eye_gaze = f"Eyes {horizontal_label}"
        else:
            eye_gaze = "Eyes Center"

        # Windows are always advanced (so they stay in step with real time),
        # but warnings are only produced once the baseline exists.
        yaw_confirmed = _hist_confirm(state["yaw_hist"], calibrated and abs(d_yaw) >= YAW_THRESHOLD, HEAD_POSE_NEED)
        pitch_confirmed = _hist_confirm(state["pitch_hist"], calibrated and abs(d_pitch) >= PITCH_THRESHOLD, HEAD_POSE_NEED)
        roll_confirmed = _hist_confirm(state["roll_hist"], calibrated and abs(d_roll) >= ROLL_THRESHOLD, HEAD_POSE_NEED)
        gaze_confirmed = _hist_confirm(
            state["gaze_hist"],
            calibrated and eye_gaze != "Eyes Center" and not eyes_closed,
            GAZE_NEED,
        )

        # ONE attention warning at a time, in priority order.
        attention = None
        if yaw_confirmed:
            attention = ("head_direction_warning", "Please look straight at the camera.")
        elif pitch_confirmed:
            attention = ("head_pitch_warning", "Please keep your face straight.")
        elif roll_confirmed:
            attention = ("head_roll_warning", "Please keep your head straight.")
        elif state["eye_closed_frames"] >= FRAME_CHECK:
            attention = ("eyes_closed_warning", "Eyes closed for too long. Please stay attentive.")
        elif gaze_confirmed:
            attention = ("gaze_warning",
                         f"Eyes are not looking at the screen ({eye_gaze}). Please look straight at your screen.")
        elif mouth_confirmed:
            attention = ("mouth_warning",
                         "Mouth movement detected. Please avoid talking during the examination.")
        # A phone / second person already explains looking away: one action,
        # one strike.
        if attention and not events:
            events.append(attention)

        warning = bool(events)
        top = events[0] if events else None

        state["latest_stats"] = {
            "ear": round(ear, 3),
            "mar": round(mar, 3),
            "closure": round(closure_percentage, 2),
            "blink_rate": blink_rate,
            "blink_count": state["blink_count"],
            "yaw": round(yaw, 2),
            "pitch": round(pitch, 2),
            "roll": round(roll, 2),
            "d_yaw": round(d_yaw, 2),
            "d_pitch": round(d_pitch, 2),
            "d_roll": round(d_roll, 2),
            "face_count": face_count,
            "status": "Warning" if warning else "Normal",
            "eyes": eyes_status,
            "mouth": mouth_status,
            "looking": looking,
            "head_pose": head_pose,
            "eye_gaze": eye_gaze,
            "gaze_ratio": round(gaze_ratio, 3),
            "phone_score": round(phone_score, 3),
            "brightness": round(brightness, 1),
            "no_face_seconds": 0,
            "calibrated": calibrated,
            "warning": warning,
            "warning_message": top[1] if top else "",
            "warning_type": top[0] if top else "",
            "warnings": [{"type": t, "message": m} for t, m in events],
        }
        return state["latest_stats"]


# ============================================================
# DATABASE INITIALIZATION
# ============================================================



def initialize_database():

    if not os.path.exists(DATABASE):

        workbook = Workbook()

        # =====================================================
        # TEACHERS
        # =====================================================

        teachers = workbook.active
        teachers.title = "Teachers"

        teachers.append([
            "Teacher ID",
            "Teacher Name",
            "Email",
            "Password"
        ])

        # =====================================================
        # EXAMS
        # =====================================================

        exams = workbook.create_sheet("Exams")

        exams.append([
            "Exam ID",
            "Teacher ID",
            "Teacher Name",
            "Subject Name",
            "Subject Code",
            "Question Number",
            "Question",
            "Option A",
            "Option B",
            "Option C",
            "Option D",
            "Correct Answer"
        ])

        # =====================================================
        # STUDENTS
        # =====================================================

        students = workbook.create_sheet("Students")

        students.append([
            "Student ID",
            "Student Name",
            "Email",
            "Password"
        ])

        # =====================================================
        # RESULTS
        # =====================================================

        results = workbook.create_sheet("Results")

        results.append([
            "Result ID",
            "Student ID",
            "Student Name",
            "Exam ID",
            "Subject Name",
            "Subject Code",
            "Total Questions",
            "Correct Answers",
            "Wrong Answers",
            "Score",
            "Percentage"
        ])

        # =====================================================
        # RESULT DETAILS
        # =====================================================

        details = workbook.create_sheet("ResultDetails")

        details.append([
            "Result ID",
            "Student ID",
            "Student Name",
            "Exam ID",
            "Subject Name",
            "Subject Code",
            "Question Number",
            "Question",
            "Student Answer",
            "Correct Answer",
            "Status"
        ])

        save_database(workbook)

        workbook.close()

        print("Complete database created.")

        return


    # =========================================================
    # EXISTING DATABASE
    # =========================================================

    workbook = load_database()

    # Add Students if missing

    if "Students" not in workbook.sheetnames:

        students = workbook.create_sheet("Students")

        students.append([
            "Student ID",
            "Student Name",
            "Email",
            "Password"
        ])


    # Add Results if missing

    if "Results" not in workbook.sheetnames:

        results = workbook.create_sheet("Results")

        results.append([
            "Result ID",
            "Student ID",
            "Student Name",
            "Exam ID",
            "Subject Name",
            "Subject Code",
            "Total Questions",
            "Correct Answers",
            "Wrong Answers",
            "Score",
            "Percentage"
        ])


    # Add ResultDetails if missing

    if "ResultDetails" not in workbook.sheetnames:

        details = workbook.create_sheet("ResultDetails")

        details.append([
            "Result ID",
            "Student ID",
            "Student Name",
            "Exam ID",
            "Subject Name",
            "Subject Code",
            "Question Number",
            "Question",
            "Student Answer",
            "Correct Answer",
            "Status"
        ])

    if "Admins" not in workbook.sheetnames:

        admins = workbook.create_sheet("Admins")

        admins.append([
            "Admin ID",
            "Admin Name",
            "Email",
            "Password"
        ])
    if "ResultDetails" not in workbook.sheetnames:

        details = workbook.create_sheet("ResultDetails")

        details.append([
            "Result ID",
            "Student ID",
            "Student Name",
            "Exam ID",
            "Subject Name",
            "Subject Code",
            "Question Number",
            "Question",
            "Student Answer",
            "Correct Answer",
            "Status"
        ])

    save_database(workbook)

    workbook.close()

    print("Database checked successfully.")



# ============================================================
# RECORDING DATABASE SUPPORT
# ============================================================



def ensure_recording_column():

    workbook = load_database()

    if "Results" not in workbook.sheetnames:
        workbook.close()
        return

    sheet = workbook["Results"]

    headers = [cell.value for cell in sheet[1]]

    if "Recording File" not in headers:

        sheet.cell(
            row=1,
            column=sheet.max_column + 1,
            value="Recording File"
        )

        save_database(workbook)

    workbook.close()


def ensure_exam_status_column():

    workbook = load_database()

    if "Results" not in workbook.sheetnames:
        workbook.close()
        return

    sheet = workbook["Results"]

    headers = [cell.value for cell in sheet[1]]

    if "Exam Status" not in headers:

        sheet.cell(
            row=1,
            column=sheet.max_column + 1,
            value="Exam Status"
        )

        save_database(workbook)

    headers = [cell.value for cell in sheet[1]]
    if "Unattempted Answers" not in headers:
        sheet.cell(row=1, column=sheet.max_column + 1, value="Unattempted Answers")
        save_database(workbook)

    workbook.close()


# ============================================================
# VIOLATION LOG SUPPORT (fullscreen exit / tab switch / window blur)
# ============================================================



def ensure_violations_sheet():

    workbook = load_database()

    if "Violations" not in workbook.sheetnames:

        sheet = workbook.create_sheet("Violations")

        sheet.append([
            "Timestamp",
            "Student ID",
            "Exam ID",
            "Violation Type",
            "Message"
        ])

        save_database(workbook)

    workbook.close()




def log_violation_to_sheet(student_id, exam_id, violation_type, message):

    try:

        workbook = load_database()

        if "Violations" not in workbook.sheetnames:

            sheet = workbook.create_sheet("Violations")

            sheet.append([
                "Timestamp",
                "Student ID",
                "Exam ID",
                "Violation Type",
                "Message"
            ])

        else:

            sheet = workbook["Violations"]

        sheet.append([
            _now_local().strftime("%Y-%m-%d %H:%M:%S"),
            student_id,
            exam_id,
            violation_type,
            message
        ])

        save_database(workbook)

        workbook.close()

    except Exception as e:

        print("Violation log write error:", str(e))


# ============================================================
# TEACHER LOGIN REQUIRED
# ============================================================



def student_login_required(function):

    @wraps(function)
    def wrapper(*args, **kwargs):

        if "student_id" not in session:

            return redirect(url_for("student_login"))

        return function(*args, **kwargs)

    return wrapper


# ============================================================
# HOME
# ============================================================




# ============================================================
# HOME — redirects straight to student login.
# There is no admin/teacher entry point anywhere in this app.
# ============================================================

@app.route("/")
def index():
    return redirect(url_for("student_login"))


# ============================================================
# ======================= STUDENT =============================
# ============================================================




@app.route("/student/register", methods=["GET", "POST"])
def student_register():

    if request.method == "POST":

        student_id = request.form["student_id"].strip()
        student_name = request.form["student_name"].strip()
        email = request.form["email"].strip()
        password = request.form["password"]

        if not student_id or not student_name or not email or not password:

            flash(
                "All fields are required.",
                "error"
            )

            return redirect(url_for("student_register"))

        workbook = load_database()

        sheet = workbook["Students"]

        for row in sheet.iter_rows(min_row=2, values_only=True):

            if row[0] == student_id:

                workbook.close()

                flash(
                    "Student ID already exists.",
                    "error"
                )

                return redirect(url_for("student_register"))

            if row[2] == email:

                workbook.close()

                flash(
                    "Email already registered.",
                    "error"
                )

                return redirect(url_for("student_register"))

        hashed_password = generate_password_hash(password)

        sheet.append([
            student_id,
            student_name,
            email,
            hashed_password
        ])

        save_database(workbook)

        workbook.close()

        flash(
            "Student registration successful. Please login.",
            "success"
        )

        return redirect(url_for("student_login"))

    return render_template("student_register.html")


# ============================================================
# STUDENT LOGIN
# ============================================================



@app.route("/student/login", methods=["GET", "POST"])
def student_login():

    if request.method == "POST":

        student_id = request.form["student_id"].strip()
        password = request.form["password"]

        workbook = load_database()

        sheet = workbook["Students"]

        for row in sheet.iter_rows(min_row=2, values_only=True):

            if row[0] == student_id:

                if check_password_hash(row[3], password):

                    session["student_id"] = row[0]
                    session["student_name"] = row[1]
                    session["student_email"] = row[2]

                    workbook.close()

                    return redirect(
                        url_for("student_dashboard")
                    )

                else:

                    workbook.close()

                    flash(
                        "Incorrect password.",
                        "error"
                    )

                    return redirect(
                        url_for("student_login")
                    )

        workbook.close()

        flash(
            "Student ID not found.",
            "error"
        )

        return redirect(url_for("student_login"))

    return render_template("student_login.html")


# ============================================================
# STUDENT DASHBOARD
# ============================================================
#@app.route('/student_dashboard1')
#def student_dashboard1():
 #   return render_template('student_dashboard.html')




def _results_attempts(workbook, student_id):
    """Return {exam_id: exam_status} for every result this student has.

    Looks columns up by header name so it works with old and new
    database.xlsx layouts (Exam ID has moved between versions).
    """
    attempts = {}
    if "Results" not in workbook.sheetnames:
        return attempts
    ws = workbook["Results"]
    headers = [str(c.value or "").strip() for c in ws[1]]

    def col(name, default):
        return headers.index(name) if name in headers else default

    i_student = col("Student ID", 1)
    i_exam = col("Exam ID", 3)
    i_status = col("Exam Status", 12)
    for row in ws.iter_rows(min_row=2, values_only=True):
        if len(row) <= max(i_student, i_exam):
            continue
        if str(row[i_student] or "").strip() != str(student_id or "").strip():
            continue
        status = row[i_status] if len(row) > i_status and row[i_status] else "Completed"
        attempts[str(row[i_exam] or "").strip()] = str(status)
    return attempts


def _parse_exam_datetime(raw_value):
    """Accept datetime objects or the common string formats (incl. 'T')."""
    if isinstance(raw_value, datetime):
        return raw_value
    if not isinstance(raw_value, str) or not raw_value.strip():
        return None
    raw_value = raw_value.strip()
    for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%dT%H:%M"):
        try:
            return datetime.strptime(raw_value, fmt)
        except ValueError:
            continue
    return None



@app.route("/student/exams/version")
@student_login_required
def student_exams_version():
    """Tiny poll target: the number changes the moment a teacher adds, edits or
    removes an exam, so the dashboard can refresh itself immediately."""
    resp = jsonify({"version": eg_exams_version()})
    resp.headers["Cache-Control"] = "no-store"
    return resp


@app.route("/internal/sync/exams", methods=["POST"])
def internal_sync_exams():
    """Local (non-Neon) mode: the admin service pushes the full Exams sheet."""
    import hmac as _hmac
    token = str(request.headers.get("X-ExamGuard-Sync-Token", ""))
    if not ADMIN_SYNC_TOKEN or not _hmac.compare_digest(token, ADMIN_SYNC_TOKEN):
        return jsonify({"success": False, "error": "Unauthorized exam sync"}), 401
    if _eg_use_neon():
        return jsonify({"success": True, "shared": True})
    try:
        payload = request.get_json(silent=True) or {}
        rows = payload.get("rows")
        if not isinstance(rows, list):
            return jsonify({"success": False, "error": "rows missing"}), 400

        def norm(r):
            t = tuple(r)
            end = len(t)
            while end > 0 and t[end - 1] in (None, ""):
                end -= 1
            return t[:end]

        incoming = [norm(r) for r in rows]
        wb = load_database()
        try:
            ws = wb["Exams"]
            current = [norm(r) for r in ws.iter_rows(min_row=2, values_only=True)
                       if r and r[0] not in (None, "")]
            if current == incoming:
                return jsonify({"success": True, "changed": False})
            if ws.max_row > 1:
                ws.delete_rows(2, ws.max_row - 1)
            for r in rows:
                ws.append(list(r))
            save_database(wb)
        finally:
            wb.close()
        _EG_LOCAL_EXAMS_VERSION["v"] += 1
        print(f"[EXAM-SYNC] Exams updated from admin ({len(rows)} rows)")
        return jsonify({"success": True, "changed": True})
    except Exception as exc:
        print("[EXAM-SYNC] failed:", exc)
        return jsonify({"success": False, "error": str(exc)}), 500


@app.route("/student/dashboard")
@student_login_required
def student_dashboard():
    student_id = session.get("student_id", "")

    # A student who reaches the dashboard has left the exam; make sure a
    # stale "locked" flag from a previous attempt cannot trap them here once
    # the keyboard was legitimately unlocked.
    workbook = load_database()
    try:
        sheet = workbook["Exams"]
        attempts = _results_attempts(workbook, student_id)
        exams = {}
        for row in sheet.iter_rows(min_row=2, values_only=True):
            exam_id = row[0]
            if exam_id in (None, "") or exam_id in exams:
                continue
            exams[exam_id] = {
                "exam_id": exam_id,
                "subject_name": row[3],
                "subject_code": row[4],
                "teacher_name": row[2],
                "from_raw": row[12] if len(row) > 12 else None,
                "until_raw": row[13] if len(row) > 13 else None,
                "duration": row[14] if len(row) > 14 else None,
            }
    finally:
        workbook.close()

    now = _now_local()
    subject_list = []
    for exam in exams.values():
        opens_at = _parse_exam_datetime(exam.pop("from_raw"))
        closes_at = _parse_exam_datetime(exam.pop("until_raw"))
        exam.pop("duration", None)
        attempt = attempts.get(str(exam["exam_id"]).strip())

        exam.update({
            "state": "live", "countdown_seconds": 0, "opens_at_label": "",
            "closes_at_label": "", "attempt_status": attempt or "",
            # backwards-compatible flags for older templates
            "finished": False, "expired": False, "countdown_target": "",
        })
        if opens_at:
            exam["opens_at_label"] = opens_at.strftime("%d %b %Y, %I:%M %p")
        if closes_at:
            exam["closes_at_label"] = closes_at.strftime("%d %b %Y, %I:%M %p")

        if attempt is not None:
            # "Completed" = submitted normally (blue); anything else = ended by
            # a violation / timeout (red "Finished").
            exam["state"] = "completed" if attempt == "Completed" else "finished"
            exam["finished"] = exam["state"] == "finished"
        elif opens_at and now < opens_at:
            exam["state"] = "upcoming"
            exam["countdown_seconds"] = max(0, int((opens_at - now).total_seconds()))
        elif closes_at and now > closes_at:
            exam["state"] = "closed"
            exam["expired"] = True
        subject_list.append(exam)

    return render_template("student_dashboard.html", subjects=subject_list, exams_version=eg_exams_version())


# ============================================================
# SUBMIT EXAM
# ============================================================



def _ensure_results_schema(workbook):
    """Ensure the Results/ResultDetails sheets contain the columns needed by
    both old databases and the current result-writing code, without changing
    the position of existing columns."""
    required_results = [
        "Result ID", "Student ID", "Student Name", "Student Email", "Exam ID", "Subject Name",
        "Subject Code", "Total Questions", "Correct Answers", "Wrong Answers",
        "Score", "Percentage", "Recording File", "Exam Status", "Unattempted Answers",
        "Submitted At"
    ]
    if "Results" not in workbook.sheetnames:
        ws = workbook.create_sheet("Results")
        for col, header in enumerate(required_results, 1):
            ws.cell(row=1, column=col, value=header)
    else:
        ws = workbook["Results"]
        headers = [c.value for c in ws[1]]
        for header in required_results:
            if header not in headers:
                ws.cell(row=1, column=ws.max_column + 1, value=header)
                headers.append(header)

    required_details = [
        "Result ID", "Student ID", "Student Name", "Exam ID", "Subject Name",
        "Subject Code", "Question Number", "Question", "Student Answer",
        "Correct Answer", "Status"
    ]
    if "ResultDetails" not in workbook.sheetnames:
        ds = workbook.create_sheet("ResultDetails")
        for col, header in enumerate(required_details, 1):
            ds.cell(row=1, column=col, value=header)
    else:
        ds = workbook["ResultDetails"]
        headers = [c.value for c in ds[1]]
        for header in required_details:
            if header not in headers:
                ds.cell(row=1, column=ds.max_column + 1, value=header)
                headers.append(header)
    return ws, ds


def _append_result_by_header(sheet, values):
    headers = [cell.value for cell in sheet[1]]
    row = [None] * len(headers)
    for key, value in values.items():
        if key in headers:
            row[headers.index(key)] = value
    sheet.append(row)




def _safe_admin_filename(value):
    name=os.path.basename(str(value or "").strip()); name=re.sub(r"[^A-Za-z0-9._-]+","_",name)
    if not name.lower().endswith(".webm"): name += ".webm"
    return name[:220] or "recording.webm"

def _is_valid_local_webm(path, min_size=2048):
    """
    Basic sanity check that a locally-assembled/uploaded recording is a
    real, non-empty WebM file (correct EBML magic bytes + a minimum
    size) before we ever treat it as "the" finished recording or push
    it to the admin server. This is what stops a partially-assembled
    or truncated recording from ever becoming the file of record.
    """
    try:
        if not path or not os.path.isfile(path):
            return False
        if os.path.getsize(path) < min_size:
            return False
        with open(path, "rb") as fh:
            magic = fh.read(4)
        return magic == bytes((0x1a, 0x45, 0xdf, 0xa3))
    except Exception:
        return False


def _post_recording_to_admin(path,exam_id,student_id,filename):
    if not ADMIN_SYNC_TOKEN or ADMIN_SYNC_TOKEN=="CHANGE_THIS_SHARED_RECORDING_SYNC_TOKEN": return False
    try:
        with open(path,"rb") as fh:
            r=requests.post(f"{ADMIN_SYNC_BASE_URL}/internal/sync/recording",headers={"X-ExamGuard-Sync-Token":ADMIN_SYNC_TOKEN},data={"exam_id":str(exam_id),"student_id":str(student_id),"filename":_safe_admin_filename(filename)},files={"recording":(filename,fh,"video/webm")},timeout=(10,300),verify=ADMIN_SYNC_VERIFY_SSL)
        return bool(r.ok and (r.json() if r.content else {}).get("success"))
    except Exception as e:
        print("[SYNC] recording upload:",e); return False

def _post_recording_chunk_to_admin(path, exam_id, student_id, filename, token, seq):
    if not path or not os.path.isfile(path) or not ADMIN_SYNC_TOKEN:
        return False
    try:
        with open(path, "rb") as fh:
            r = requests.post(
                f"{ADMIN_SYNC_BASE_URL}/internal/sync/recording-chunk",
                headers={"X-ExamGuard-Sync-Token": ADMIN_SYNC_TOKEN},
                data={
                    "exam_id": str(exam_id),
                    "student_id": str(student_id),
                    "filename": _safe_admin_filename(filename),
                    "recording_token": str(token),
                    "sequence": str(seq),
                },
                files={"chunk": (f"chunk_{seq}.webm", fh, "video/webm")},
                timeout=(4, 20),
                verify=ADMIN_SYNC_VERIFY_SSL,
            )
        payload = r.json() if r.content else {}
        if not (r.ok and payload.get("success")):
            print(f"[SYNC] recording chunk rejected: HTTP {r.status_code} {payload}")
        return bool(r.ok and payload.get("success"))
    except Exception as e:
        print("[SYNC] recording chunk:", e)
        return False


# Live forwarding: every 2-second chunk is passed on to the admin server while
# the exam is still running, so nothing big is left to upload at the end.
FWD_STATE = {}
FWD_STATE_LOCK = threading.Lock()
FWD_FOLDER = os.path.join(RECORDINGS_FOLDER, ".examguard_fwd")
os.makedirs(FWD_FOLDER, exist_ok=True)
RECORDING_CHUNK_SYNC_QUEUE = __import__('queue').Queue()
RECORDING_CHUNK_SYNC_THREAD_STARTED = False
RECORDING_CHUNK_SYNC_START_LOCK = threading.Lock()


def _recording_chunk_sync_worker():
    while True:
        item = RECORDING_CHUNK_SYNC_QUEUE.get()
        if item is None:
            RECORDING_CHUNK_SYNC_QUEUE.task_done()
            break
        path, exam_id, student_id, filename, token, seq = item
        try:
            ok = False
            for attempt in range(1, 8):
                if not os.path.isfile(path):
                    ok = True            # already delivered earlier
                    break
                if _post_recording_chunk_to_admin(path, exam_id, student_id, filename, token, seq):
                    ok = True
                    break
                time.sleep(min(4, attempt))
            if ok:
                try: os.remove(path)
                except OSError: pass
                with FWD_STATE_LOCK:
                    FWD_STATE.setdefault(token, {"queued": set(), "sent": set()})["sent"].add(int(seq))
            else:
                print(f"[SYNC] Recording chunk remains queued: {token}:{seq}")
        finally:
            RECORDING_CHUNK_SYNC_QUEUE.task_done()


def _start_recording_chunk_sync_worker():
    global RECORDING_CHUNK_SYNC_THREAD_STARTED
    with RECORDING_CHUNK_SYNC_START_LOCK:
        if not RECORDING_CHUNK_SYNC_THREAD_STARTED:
            for i in range(4):
                threading.Thread(target=_recording_chunk_sync_worker, daemon=True, name=f"recording-sync-{i+1}").start()
            RECORDING_CHUNK_SYNC_THREAD_STARTED = True


def _queue_recording_chunk_for_admin(path, exam_id, student_id, filename, token, seq):
    if not path or not os.path.isfile(path):
        return
    _start_recording_chunk_sync_worker()
    RECORDING_CHUNK_SYNC_QUEUE.put((path, str(exam_id), str(student_id), str(filename), str(token), int(seq)))


def _post_recording_finalize_to_admin(exam_id, student_id, filename, token, expected_last_seq):
    if not ADMIN_SYNC_TOKEN:
        return False
    try:
        r = requests.post(
            f"{ADMIN_SYNC_BASE_URL}/internal/sync/recording-finalize",
            headers={"X-ExamGuard-Sync-Token": ADMIN_SYNC_TOKEN},
            data={
                "exam_id": str(exam_id),
                "student_id": str(student_id),
                "filename": _safe_admin_filename(filename),
                "recording_token": str(token),
                "expected_last_seq": str(expected_last_seq),
            },
            timeout=(4, 30),
            verify=ADMIN_SYNC_VERIFY_SSL,
        )
        payload = r.json() if r.content else {}
        if r.ok and payload.get("success"):
            print("[SYNC] Recording finalized on admin:", filename)
            return True
        print("[SYNC] Recording finalize rejected:", payload)
    except Exception as e:
        print("[SYNC] recording finalize:", e)
    return False


def _queue_recording_finalize_for_admin(exam_id, student_id, filename, token, expected_last_seq):
    def worker():
        for attempt in range(1, 10):
            if _post_recording_finalize_to_admin(exam_id, student_id, filename, token, expected_last_seq):
                return
            time.sleep(min(8, attempt))
    threading.Thread(target=worker, daemon=True, name="recording-finalize-sync").start()


RECORDING_STATUS = {}
RECORDING_STATUS_LOCK = threading.Lock()
RECORDING_PUSH_RUNNING = set()
RECORDING_READY_FALLBACK_SECONDS = int(os.environ.get("RECORDING_READY_FALLBACK_SECONDS", "25"))


def _rec_key(student_id, exam_id):
    return f"{student_id}:{exam_id}"


def _rec_status_set(student_id, exam_id, state, detail=""):
    key = _rec_key(student_id, exam_id)
    with RECORDING_STATUS_LOCK:
        cur = RECORDING_STATUS.setdefault(key, {"started_at": time.time()})
        cur.update({"state": state, "detail": detail, "updated_at": time.time()})


def _rec_status_get(student_id, exam_id):
    with RECORDING_STATUS_LOCK:
        return dict(RECORDING_STATUS.get(_rec_key(student_id, exam_id), {}))


def _recording_ready(student_id, exam_id):
    """True when the keyboard may be unlocked: the recording reached the admin,
    there is no recording to wait for, or it has been retrying for a long time
    (the background thread keeps going either way)."""
    st = _rec_status_get(student_id, exam_id)
    if not st:
        return True
    if st.get("state") in ("done", "none", "failed"):
        return True
    return (time.time() - st.get("started_at", time.time())) > RECORDING_READY_FALLBACK_SECONDS


def _queue_recording_for_admin(path,exam_id,student_id,filename,try_immediately=False):
    """Push the assembled recording to the admin server in the background.

    Never blocks the student: a worker thread retries with back-off for
    several minutes (the admin service on Render may be cold-starting), and a
    marker file lets it resume after a restart.
    """
    if not path or not os.path.isfile(path): return
    filename=_safe_admin_filename(filename); marker=os.path.join(ADMIN_SYNC_FOLDER,filename+".json")
    try:
        with open(marker,"w",encoding="utf-8") as fh: json.dump({"path":path,"exam_id":str(exam_id),"student_id":str(student_id),"filename":filename},fh)
    except Exception as e: print("[SYNC] recording queue:",e)

    run_key = filename
    with RECORDING_STATUS_LOCK:
        if run_key in RECORDING_PUSH_RUNNING:
            return
        RECORDING_PUSH_RUNNING.add(run_key)
    _rec_status_set(student_id, exam_id, "uploading", "Sending the recording to the examiner.")

    def worker():
        try:
            for attempt in range(1, 61):
                if _post_recording_to_admin(path,exam_id,student_id,filename):
                    try: os.remove(marker)
                    except OSError: pass
                    _rec_status_set(student_id, exam_id, "done", "Recording uploaded.")
                    print("[SYNC] Recording synced to admin:",filename)
                    return
                _rec_status_set(student_id, exam_id, "uploading", f"Retrying upload (attempt {attempt})...")
                time.sleep(min(15, 2 + attempt * 2))
            _rec_status_set(student_id, exam_id, "failed", "Upload will keep retrying in the background.")
            print("[SYNC] Recording remains queued:",filename)
        finally:
            with RECORDING_STATUS_LOCK:
                RECORDING_PUSH_RUNNING.discard(run_key)
    threading.Thread(target=worker,daemon=True,name="recording-push").start()

def _queue_result_for_admin(payload):
    if not ADMIN_SYNC_TOKEN or ADMIN_SYNC_TOKEN=="CHANGE_THIS_SHARED_RECORDING_SYNC_TOKEN": return
    rid=str(payload.get("result_id","")).strip()
    if not rid: return
    marker=os.path.join(ADMIN_RESULT_SYNC_FOLDER,re.sub(r"[^A-Za-z0-9_-]","_",rid)+".json")
    try:
        with open(marker,"w",encoding="utf-8") as fh: json.dump(payload,fh)
    except Exception as e: print("[SYNC] result queue:",e)
    def worker():
        for attempt in range(1,13):
            try:
                r=requests.post(f"{ADMIN_SYNC_BASE_URL}/internal/sync/result",headers={"X-ExamGuard-Sync-Token":ADMIN_SYNC_TOKEN,"Content-Type":"application/json"},json=payload,timeout=(5,30),verify=ADMIN_SYNC_VERIFY_SSL)
                if r.ok and (r.json() if r.content else {}).get("success"):
                    try: os.remove(marker)
                    except OSError: pass
                    print("[SYNC] Result synced to admin:",rid); return
            except Exception as e: print("[SYNC] result upload:",e)
            time.sleep(min(10,attempt*2))
    threading.Thread(target=worker,daemon=True).start()

# Each student gets at most one live-frame sync worker. New frames replace the
# pending frame rather than spawning another network request. This prevents
# old JPEGs from piling up when the admin server/network is temporarily slow.
LIVE_FRAME_SYNC_STATE = {}
LIVE_FRAME_SYNC_STATE_LOCK = threading.Lock()
LIVE_FRAME_SYNC_INTERVAL = 2.0

LIVE_VIOLATION_STATE = {}
LIVE_VIOLATION_LOCK = threading.Lock()
_TERMINATION_TYPES = {"max_warnings_reached", "fullscreen_exit", "tab_switch_autoend", "time_expired", "no_face_timeout"}


def _note_violation(student_id, exam_id, vtype, message):
    sid = str(student_id or "")
    if not sid:
        return
    with LIVE_VIOLATION_LOCK:
        entry = LIVE_VIOLATION_STATE.setdefault(sid, {"count": 0, "last": "", "exam_id": str(exam_id or ""), "terminated": False})
        if entry.get("exam_id") != str(exam_id or ""):
            entry.update({"count": 0, "last": "", "exam_id": str(exam_id or ""), "terminated": False})
        if vtype in _TERMINATION_TYPES:
            entry["terminated"] = True
        else:
            entry["count"] += 1
        entry["last"] = f"{vtype}: {message}"[:240]


def _live_violation_fields(student_id):
    with LIVE_VIOLATION_LOCK:
        entry = dict(LIVE_VIOLATION_STATE.get(str(student_id or ""), {}))
    return {
        "violation_count": int(entry.get("count", 0)),
        "last_violation": entry.get("last", ""),
        "terminated": bool(entry.get("terminated", False)),
    }


def _safe_live_sync_id(value):
    return re.sub(r"[^A-Za-z0-9_-]","_",str(value or ""))[:120] or "student"

# ============================================================
# LIVE ADMIN DISCOVERY
# ============================================================
# Do not assume the admin computer has a fixed IP. In a two-PC LAN
# deployment, the old hard-coded 192.168.1.24 address could silently
# send every live heartbeat/frame to the wrong machine. We first try
# the configured address, then localhost (same-PC deployment), then
# probe only the student's own private /24 LAN for the admin port.
LIVE_ADMIN_URL_CACHE = None
LIVE_ADMIN_URL_LOCK = threading.Lock()
LIVE_ADMIN_DISCOVERY_TIMEOUT = 0.35


def _admin_url_candidates():
    candidates = []
    configured = str(os.environ.get("EXAMGUARD_ADMIN_BASE_URL", "")).strip().rstrip("/")
    if configured:
        candidates.append(configured)
    # Keep the historical default as a candidate, but never depend on it.
    candidates.append("https://192.168.1.24:5050")
    candidates.append("https://127.0.0.1:5050")
    candidates.append("https://localhost:5050")
    try:
        local_ip = _local_lan_ip()
        parts = local_ip.split(".")
        if len(parts) == 4 and all(x.isdigit() for x in parts):
            prefix = ".".join(parts[:3])
            # Probe the local /24 in parallel. This is only LAN discovery,
            # never an Internet scan.
            for last in range(1, 255):
                candidates.append(f"https://{prefix}.{last}:5050")
    except Exception:
        pass
    out=[]
    seen=set()
    for url in candidates:
        url=url.rstrip("/")
        if url and url not in seen:
            seen.add(url); out.append(url)
    return out


def _probe_admin_url(url):
    try:
        r=requests.get(
            f"{url}/admin/live-status",
            timeout=LIVE_ADMIN_DISCOVERY_TIMEOUT,
            verify=ADMIN_SYNC_VERIFY_SSL,
        )
        # 200 means this is our admin endpoint. A redirect is also enough
        # to identify a Flask admin server; authenticated status will still
        # be supplied by the normal browser session later.
        return r.status_code in (200, 302, 303)
    except Exception:
        return False


def _get_admin_sync_url():
    global LIVE_ADMIN_URL_CACHE
    if ADMIN_URL_EXPLICIT:
        return ADMIN_SYNC_BASE_URL
    with LIVE_ADMIN_URL_LOCK:
        if LIVE_ADMIN_URL_CACHE:
            return LIVE_ADMIN_URL_CACHE

    candidates = _admin_url_candidates()
    # Check the cheap/high-probability addresses first.
    for url in candidates[:4]:
        if _probe_admin_url(url):
            with LIVE_ADMIN_URL_LOCK:
                LIVE_ADMIN_URL_CACHE = url
            print("[LIVE] Admin server discovered:", url)
            return url

    # Probe LAN candidates concurrently so discovery does not block the exam.
    import concurrent.futures
    lan = candidates[4:]
    if lan:
        with concurrent.futures.ThreadPoolExecutor(max_workers=32) as ex:
            futures = {ex.submit(_probe_admin_url, u): u for u in lan}
            for fut in concurrent.futures.as_completed(futures):
                try:
                    if fut.result():
                        url=futures[fut]
                        with LIVE_ADMIN_URL_LOCK:
                            LIVE_ADMIN_URL_CACHE = url
                        print("[LIVE] Admin server discovered:", url)
                        return url
                except Exception:
                    pass
    print("[LIVE] Could not discover admin server. Set EXAMGUARD_ADMIN_BASE_URL on the student PC.")
    return ""


def _post_live_frame_to_admin(frame_path,student_id,payload):
    if not LIVE_SYNC_TOKEN: return False
    admin_url = _get_admin_sync_url()
    if not admin_url: return False
    try:
        with open(frame_path,"rb") as fh:
            r=requests.post(
                f"{admin_url}/internal/sync/live-frame",
                headers={"X-ExamGuard-Sync-Token":LIVE_SYNC_TOKEN},
                data={
                    "student_id":str(student_id),
                    "student_name":str(payload.get("student_name","")),
                    "exam_id":str(payload.get("exam_id","")),
                    "last_seen":str(payload.get("last_seen",time.time())),
                    "status":str(payload.get("status","")),
                    "warning":str(bool(payload.get("warning",False))).lower(),
                    "warning_message":str(payload.get("warning_message","")),
                    "student_signal_base_url":str(payload.get("student_signal_base_url", "")),
                    "violation_count":str(payload.get("violation_count", 0)),
                    "last_violation":str(payload.get("last_violation", "")),
                    "terminated":str(bool(payload.get("terminated", False))).lower(),
                },
                files={"frame":("live.jpg",fh,"image/jpeg")},
                timeout=(4,12),
                verify=ADMIN_SYNC_VERIFY_SSL,
            )
        return bool(r.ok)
    except Exception as e:
        print("[SYNC] live frame:",e); return False

def _schedule_live_frame_sync(frame_path,student_id,payload):
    if not os.path.isfile(frame_path):
        return
    sid = str(student_id)
    with LIVE_FRAME_SYNC_STATE_LOCK:
        state = LIVE_FRAME_SYNC_STATE.get(sid)
        if state is None:
            state = {"running": False, "pending": False, "payload": payload}
            LIVE_FRAME_SYNC_STATE[sid] = state
        state["pending"] = True
        state["payload"] = payload
        if state["running"]:
            return
        state["running"] = True

    def worker():
        try:
            while True:
                with LIVE_FRAME_SYNC_STATE_LOCK:
                    state = LIVE_FRAME_SYNC_STATE.get(sid)
                    if not state or not state.get("pending"):
                        if state:
                            state["running"] = False
                            LIVE_FRAME_SYNC_STATE.pop(sid, None)
                        return
                    state["pending"] = False
                # The frame path is stable and atomically replaced by the
                # newest snapshot. Read the newest payload too; this worker
                # never sends a backlog of stale frames/status.
                with LIVE_FRAME_SYNC_STATE_LOCK:
                    state = LIVE_FRAME_SYNC_STATE.get(sid)
                    current_payload = dict(state.get("payload", payload)) if state else dict(payload)
                _post_live_frame_to_admin(frame_path, sid, current_payload)
                time.sleep(LIVE_FRAME_SYNC_INTERVAL)
        finally:
            with LIVE_FRAME_SYNC_STATE_LOCK:
                state = LIVE_FRAME_SYNC_STATE.get(sid)
                if state:
                    state["running"] = False
                    if not state.get("pending"):
                        LIVE_FRAME_SYNC_STATE.pop(sid, None)

    threading.Thread(target=worker, daemon=True, name=f"live-frame-sync-{_safe_live_sync_id(sid)}").start()

def _post_live_heartbeat_to_admin(student_id,payload):
    if not LIVE_SYNC_TOKEN: return False
    admin_url = _get_admin_sync_url()
    if not admin_url: return False
    try:
        r=requests.post(
            f"{admin_url}/internal/sync/live-heartbeat",
            headers={"X-ExamGuard-Live-Token":LIVE_SYNC_TOKEN},
            data={
                "student_id":str(student_id),
                "student_name":str(payload.get("student_name","")),
                "exam_id":str(payload.get("exam_id","")),
                "last_seen":str(payload.get("last_seen",time.time())),
                "status":str(payload.get("status","")),
                "warning":str(bool(payload.get("warning",False))).lower(),
                "warning_message":str(payload.get("warning_message","")),
                "student_signal_base_url":str(payload.get("student_signal_base_url", "")),
                "violation_count":str(payload.get("violation_count", 0)),
                "last_violation":str(payload.get("last_violation", "")),
                "terminated":str(bool(payload.get("terminated", False))).lower(),
            },
            timeout=(4,10),
            verify=ADMIN_SYNC_VERIFY_SSL,
        )
        return bool(r.ok)
    except Exception as e:
        print("[SYNC] live heartbeat:",e)
        return False

# FIX: the browser sends a monitoring frame every 400ms (see
# startMonitoringLoop), and until now EVERY single one of those
# frames triggered two more network calls out to the separate admin
# server (one heartbeat POST + one JPEG frame POST) — roughly 5
# requests/second, per student, each opening a brand-new HTTPS
# connection. Neither Flask app runs with threaded=True, so the
# admin server can only handle one request at a time; at that
# volume it falls permanently behind, every one of those requests
# times out (1.5-4s timeouts), and the admin's live_frames folder
# never gets updated — which is exactly why Live Monitoring always
# showed zero students, even while the student's own warnings/exam
# flow (which never depended on this) worked fine. This does not
# change monitoring/warning frequency for the student's own exam
# experience at all — only how often that status gets relayed to
# the separate admin server, which only needs to be "fresh within a
# few seconds" anyway (LIVE_ACTIVE_WINDOW_SECONDS is 8s).
LIVE_SYNC_MIN_INTERVAL_SECONDS = 1.0
_last_live_sync_at = {}
_last_live_sync_lock = threading.Lock()


def _live_sync_due(student_id, kind="hb"):
    key = f"{student_id}:{kind}"
    now = time.time()
    with _last_live_sync_lock:
        last = _last_live_sync_at.get(key, 0)
        if now - last < LIVE_SYNC_MIN_INTERVAL_SECONDS:
            return False
        _last_live_sync_at[key] = now
        return True


def _schedule_live_heartbeat_sync(student_id,payload):
    if not _live_sync_due(student_id):
        return
    threading.Thread(target=_post_live_heartbeat_to_admin,args=(student_id,payload),daemon=True).start()

def _post_live_audio_to_admin(audio_path,student_id):
    if not LIVE_SYNC_TOKEN: return False
    try:
        with open(audio_path,"rb") as fh:
            r=requests.post(
                f"{_get_admin_sync_url() or ADMIN_SYNC_BASE_URL}/internal/sync/live-audio",
                headers={"X-ExamGuard-Sync-Token":LIVE_SYNC_TOKEN},
                data={"student_id":str(student_id)},
                files={"audio":("chunk.webm",fh,"audio/webm")},
                timeout=(4,12),
                verify=ADMIN_SYNC_VERIFY_SSL,
            )
        return bool(r.ok)
    except Exception as e:
        print("[SYNC] live audio:",e); return False

def _retry_pending_admin_syncs():
    for p in list(Path(ADMIN_SYNC_FOLDER).glob("*.json")):
        try:
            d=json.loads(p.read_text(encoding="utf-8")); _queue_recording_for_admin(d.get("path",""),d.get("exam_id",""),d.get("student_id",""),d.get("filename",""))
        except Exception: pass
    for p in list(Path(ADMIN_RESULT_SYNC_FOLDER).glob("*.json")):
        try: _queue_result_for_admin(json.loads(p.read_text(encoding="utf-8")))
        except Exception: pass

@app.route("/student/exam/<exam_id>/submit", methods=["POST"])
@student_login_required
def submit_exam(exam_id):

    workbook = load_database()

    _already = _results_attempts(workbook, session.get("student_id", "")).get(str(exam_id).strip())
    if _already is not None:
        workbook.close()
        session["kb_locked"] = True
        session["kb_locked_exam"] = exam_id
        return _render_exam_done(exam_id, "", _already)

    exam_sheet = workbook["Exams"]

    questions = []

    subject_name = ""
    subject_code = ""
    teacher_id = ""

    # =========================================================
    # GET EXAM QUESTIONS
    # =========================================================

    for row in exam_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        if row[0] == exam_id:

            teacher_id = row[1]

            subject_name = row[3]

            subject_code = row[4]

            questions.append({

                "number": row[5],

                "question": row[6],

                "option_a": row[7],

                "option_b": row[8],

                "option_c": row[9],

                "option_d": row[10],

                "correct_answer": row[11]

            })


    if not questions:

        workbook.close()

        flash(
            "Exam not found.",
            "error"
        )

        return redirect(
            url_for("student_dashboard")
        )


    # =========================================================
    # CREATE RESULT ID
    # =========================================================

    result_id = "RESULT-" + uuid.uuid4().hex[:8].upper()

    recording_file = request.form.get("recording_file", "").strip()
    recording_token = request.form.get("recording_token", "").strip()

    # Never trust a browser-supplied filename by itself. If the file is not
    # physically present, fall back to the server-side recording token.
    if recording_file:
        candidate = os.path.join(RECORDINGS_FOLDER, os.path.basename(recording_file))
        if not os.path.isfile(candidate):
            recording_file = ""

    # Recording finalization is intentionally asynchronous.  The student
    # must never wait for video assembly before seeing the result page.
    # The recording token lets a background worker finish the already-uploaded
    # parts (including the final chunk that may still be in flight).
    if recording_token and not recording_file:
        try:
            part_dir = os.path.join(RECORDINGS_FOLDER, ".examguard_parts", recording_token)
            meta = _load_recording_meta(part_dir) if os.path.isdir(part_dir) else None
            if meta and str(meta.get("student_id", "")) == str(session.get("student_id", "")) and str(meta.get("exam_id", "")) == str(exam_id):
                fname = os.path.basename(str(meta.get("filename", "")).strip())
                expected_last_seq_raw = request.form.get("recording_expected_last_seq", "")
                expected_last_seq = int(expected_last_seq_raw) if expected_last_seq_raw.isdigit() else None
                if fname:
                    recording_file = fname
                threading.Thread(
                    target=_background_finalize_recording,
                    args=(exam_id, session.get("student_id", ""), recording_token, expected_last_seq),
                    daemon=True,
                ).start()
        except Exception as rec_err:
            print("Submit recording background schedule error:", rec_err)

    termination_reason_raw = request.form.get("termination_reason", "").strip()

    TERMINATION_LABELS = {
        "fullscreen_exit": "Terminated: Exited Fullscreen",
        "tab_switch_autoend": "Terminated: Switched Tabs/Window",
        "max_warnings_reached": "Terminated: Maximum Warnings Reached",
        "time_expired": "Time Expired — Auto Submitted",
        "no_face_timeout": "Terminated: Face Not Visible",
    }

    exam_status = TERMINATION_LABELS.get(termination_reason_raw, "Completed")
    was_terminated_for_violation = termination_reason_raw in TERMINATION_LABELS


    # =========================================================
    # CALCULATE ANSWERS
    # =========================================================

    correct_count = 0
    wrong_count = 0
    unattempted_count = 0

    result_questions = []

    for question in questions:
        number = question["number"]
        selected_answer = request.form.get(f"question_{number}")
        correct_answer = question["correct_answer"]

        if selected_answer is None or not str(selected_answer).strip():
            selected_answer = "Not Answered"
            status = "Unattempted"
            unattempted_count += 1
        elif selected_answer == correct_answer:
            status = "Correct"
            correct_count += 1
        else:
            status = "Wrong"
            wrong_count += 1

        result_questions.append({**question, "selected_answer": selected_answer, "status": status})

    # =========================================================
    # SCORE
    # =========================================================

    total_questions = len(questions)


    if total_questions > 0:

        percentage = round(
            (correct_count / total_questions) * 100,
            2
        )

    else:

        percentage = 0


    # =========================================================
    # SAVE SUMMARY RESULT — align by column name so older database.xlsx
    # files cannot break timeout/auto-submit when columns were added later.
    # =========================================================
    result_sheet, details_sheet = _ensure_results_schema(workbook)

    submitted_at = _now_local().strftime("%Y-%m-%d %H:%M:%S")

    _append_result_by_header(result_sheet, {
        "Result ID": result_id,
        "Student ID": session["student_id"],
        "Student Name": session["student_name"],
        "Student Email": session.get("student_email", ""),
        "Exam ID": exam_id,
        "Subject Name": subject_name,
        "Subject Code": subject_code,
        "Total Questions": total_questions,
        "Correct Answers": correct_count,
        "Wrong Answers": wrong_count,
        "Score": f"{correct_count}/{total_questions}",
        "Percentage": percentage,
        "Recording File": recording_file,
        "Exam Status": exam_status,
        "Unattempted Answers": unattempted_count,
        "Submitted At": submitted_at,
    })

    for q in result_questions:
        _append_result_by_header(details_sheet, {
            "Result ID": result_id,
            "Student ID": session["student_id"],
            "Student Name": session["student_name"],
            "Exam ID": exam_id,
            "Subject Name": subject_name,
            "Subject Code": subject_code,
            "Question Number": q["number"],
            "Question": q["question"],
            "Student Answer": q["selected_answer"],
            "Correct Answer": q["correct_answer"],
            "Status": q["status"],
        })

    # Save in one operation. If the workbook is temporarily busy (for
    # example, the teacher/admin process is reading it at the same moment),
    # retry a few times instead of surfacing a white 500 page.
    save_error = None
    workbook_ready_to_close = workbook
    for attempt in range(3):
        try:
            save_database(workbook)
            save_error = None
            break
        except (PermissionError, OSError, ValueError) as exc:
            save_error = exc
            time.sleep(0.35 * (attempt + 1))
    if save_error is not None:
        try:
            workbook.close()
        except Exception:
            pass
        return (
            "<h2 style='font-family:Segoe UI,Arial,sans-serif;padding:40px'>"
            "Your answers could not be saved to the results database. "
            "Please close database.xlsx if it is open in Excel and try again."
            "</h2>", 503
        )
    workbook.close()

    # Exam finished — remove from the admin system's "live now" list
    # and clear the active-exam marker for this session
    try:
        sid = session.get("student_id", "")
        for ext in (".jpg", ".json", "_audio.webm"):
            p = os.path.join(LIVE_FRAMES_FOLDER, f"{sid}{ext}")
            if os.path.exists(p):
                os.remove(p)
    except Exception as cleanup_err:
        print("Live frame cleanup error:", str(cleanup_err))

    # Keep a small server-side marker so the result page can remain locked
    # until the authorized password is entered.
    session["result_lock_exam_id"] = exam_id
    audio_key = f"{session.get('student_id', '')}:{exam_id}"
    with AUDIO_HIGH_SAMPLE_LOCK:
        AUDIO_HIGH_SAMPLE_COUNTS.pop(audio_key, None)
        AUDIO_NOISE_FLOORS.pop(audio_key, None)
    # FIX: release this attempt's isolated face-tracking state (and
    # close its MediaPipe FaceMesh instance) as soon as the exam
    # ends, instead of leaving it in the registry until the idle
    # sweep gets to it. Keeps memory/handles bounded under sustained,
    # long-running use with many students over the course of a day.
    _release_monitor_state(audio_key)
    session.pop("current_exam_id", None)
    session.pop("current_exam_duration_minutes", None)

    _queue_result_for_admin({
        "result_id": result_id,
        "student_id": session.get("student_id", ""),
        "student_name": session.get("student_name", ""),
        "student_email": session.get("student_email", ""),
        "exam_id": exam_id,
        "subject_name": subject_name,
        "subject_code": subject_code,
        "total_questions": total_questions,
        "correct_answers": correct_count,
        "wrong_answers": wrong_count,
        "score": f"{correct_count}/{total_questions}",
        "percentage": percentage,
        "recording_file": recording_file,
        "exam_status": exam_status,
        "unattempted_answers": unattempted_count,
        "submitted_at": submitted_at,
        "details": [
            {"number":q["number"],"question":q["question"],"selected_answer":q["selected_answer"],"correct_answer":q["correct_answer"],"status":q["status"]}
            for q in result_questions
        ],
    })

    # =========================================================
    # NO RESULT FOR THE STUDENT - on-screen keyboard unlock page instead
    # =========================================================
    session["kb_locked"] = True
    session["kb_locked_exam"] = exam_id
    if recording_token and not _rec_status_get(session.get("student_id", ""), exam_id):
        _rec_status_set(session.get("student_id", ""), exam_id, "processing", "Receiving the last part of your exam video.")
    elif not recording_token and not recording_file:
        _rec_status_set(session.get("student_id", ""), exam_id, "none", "No recording for this attempt.")
    return _render_exam_done(exam_id, subject_name, exam_status)



# ============================================================
# STUDENT LOGOUT
# ============================================================



@app.route("/student/logout")
def student_logout():

    session.pop("student_id", None)
    session.pop("student_name", None)
    session.pop("student_email", None)
    session.pop("result_lock_exam_id", None)

    return redirect(url_for("index"))


# ============================================================
# TEACHER LOGOUT
# ============================================================




def _safe_recording_component(value, fallback="x"):
    text = "".join(c for c in str(value) if c.isalnum() or c in "-_")
    return text or fallback


def _recording_meta_path(part_dir):
    return os.path.join(part_dir, "meta.json")


def _load_recording_meta(part_dir):
    try:
        with open(_recording_meta_path(part_dir), "r", encoding="utf-8") as fh:
            data = json.load(fh)
        return data if isinstance(data, dict) else None
    except Exception:
        return None


def _save_recording_meta(part_dir, meta):
    path = _recording_meta_path(part_dir)
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        json.dump(meta, fh)
    os.replace(tmp, path)


def _get_recording_assembly_lock(token):
    with RECORDING_ASSEMBLY_LOCK:
        lock = RECORDING_ASSEMBLY_LOCKS.get(token)
        if lock is None:
            lock = threading.Lock()
            RECORDING_ASSEMBLY_LOCKS[token] = lock
        return lock


def _assemble_ready_recording_parts(part_dir, meta):
    token = str(meta["token"])
    lock = _get_recording_assembly_lock(token)
    with lock:
        partial_path = os.path.join(part_dir, "assembled.partial.webm")
        next_seq = int(meta.get("next_seq", 0))
        while True:
            part_path = os.path.join(part_dir, f"{next_seq:08d}.part")
            if not os.path.isfile(part_path):
                break
            with open(partial_path, "ab") as out, open(part_path, "rb") as src:
                shutil.copyfileobj(src, out, length=1024 * 1024)
            next_seq += 1
            meta["next_seq"] = next_seq
            meta["updated_at"] = _now_local().isoformat(timespec="seconds")
            _save_recording_meta(part_dir, meta)
            try:
                os.remove(part_path)
            except OSError:
                pass
        return next_seq, partial_path



def _deliver_recording_to_admin(final_path, exam_id, student_id, filename, token, expected_last_seq=None):
    """Hand the finished recording to the admin server.

    Fast path: the chunks were already forwarded live, so only a tiny
    "assemble" call is needed. If anything is missing it re-sends just those
    chunks. If that still fails, the complete file is pushed (old behaviour),
    so a recording is never lost.
    """
    key = (str(student_id), str(exam_id))
    def worker():
        try:
            _rec_status_set(student_id, exam_id, "uploading", "Sending the recording to the examiner.")
            deadline = time.time() + 75
            fwd_dir = os.path.join(FWD_FOLDER, str(token))
            while time.time() < deadline:
                with FWD_STATE_LOCK:
                    st = FWD_STATE.get(token, {"queued": set(), "sent": set()})
                    queued, sent = set(st["queued"]), set(st["sent"])
                last = expected_last_seq if expected_last_seq is not None else (max(queued) if queued else None)
                if last is None:
                    break
                if queued and queued.issubset(sent) and all(i in queued for i in range(0, last + 1)):
                    break
                # Chunks the browser uploaded but that were never queued (e.g. after a restart).
                for i in range(0, last + 1):
                    fp = os.path.join(fwd_dir, f"{i:08d}.part")
                    if i not in sent and i not in queued and os.path.isfile(fp):
                        with FWD_STATE_LOCK:
                            FWD_STATE.setdefault(token, {"queued": set(), "sent": set()})["queued"].add(i)
                        _queue_recording_chunk_for_admin(fp, exam_id, student_id, filename, token, i)
                time.sleep(0.25)
            last = expected_last_seq
            if last is None:
                with FWD_STATE_LOCK:
                    q = FWD_STATE.get(token, {}).get("queued", set())
                last = max(q) if q else None
            if last is not None:
                for attempt in range(1, 6):
                    if _post_recording_finalize_to_admin(exam_id, student_id, filename, token, last):
                        _rec_status_set(student_id, exam_id, "done", "Recording uploaded.")
                        with FWD_STATE_LOCK:
                            FWD_STATE.pop(token, None)
                        shutil.rmtree(fwd_dir, ignore_errors=True)
                        return
                    time.sleep(min(3, attempt))
            print("[SYNC] Live-forwarded recording incomplete; sending the full file instead:", filename)
        except Exception as exc:
            print("[SYNC] deliver recording:", exc)
        _queue_recording_for_admin(final_path, exam_id, student_id, filename)
    threading.Thread(target=worker, daemon=True, name="recording-deliver").start()


@app.route("/student/exam/<exam_id>/upload-recording-chunk", methods=["POST"])
@student_login_required
def upload_exam_recording_chunk(exam_id):
    try:
        video = request.files.get("video")
        token = str(request.headers.get("X-Recording-Token", "")).strip()
        seq_raw = str(request.headers.get("X-Recording-Seq", "")).strip()
        if not video:
            return jsonify({"success": False, "error": "No recording chunk received"}), 400
        if not token or not re.fullmatch(r"[A-Za-z0-9_-]{16,80}", token):
            return jsonify({"success": False, "error": "Invalid recording token"}), 400
        if not seq_raw.isdigit():
            return jsonify({"success": False, "error": "Invalid recording sequence"}), 400
        seq = int(seq_raw)
        if seq < 0 or seq > 1000000:
            return jsonify({"success": False, "error": "Invalid recording sequence"}), 400

        safe_student = _safe_recording_component(session.get("student_id", "student"), "student")
        safe_exam = _safe_recording_component(exam_id, "exam")
        part_dir = os.path.join(RECORDINGS_FOLDER, ".examguard_parts", token)
        os.makedirs(part_dir, exist_ok=True)
        meta = _load_recording_meta(part_dir)
        if meta is None:
            # FIX: filename used to include a timestamp + random uuid,
            # so every exam attempt (and every retry that didn't find
            # this exact token's meta yet) could mint a brand new name.
            # Since a student can only take a given exam once, the
            # (student, exam) pair alone is already a unique, stable
            # identity for this recording — using only that means
            # every code path that ever needs to name this recording
            # converges on the exact same filename, so there is only
            # ever one file for it, and an older leftover recording
            # from before this fix (if any) is cleanly replaced by the
            # correct current one instead of accumulating alongside it.
            filename = f"{safe_student}_{safe_exam}.webm"
            meta = {
                "token": token,
                "student_id": str(session.get("student_id", "")),
                "exam_id": str(exam_id),
                "filename": filename,
                "next_seq": 0,
                "created_at": _now_local().isoformat(timespec="seconds"),
                "updated_at": _now_local().isoformat(timespec="seconds"),
            }
            _save_recording_meta(part_dir, meta)
        elif (str(meta.get("student_id", "")) != str(session.get("student_id", ""))
              or str(meta.get("exam_id", "")) != str(exam_id)):
            return jsonify({"success": False, "error": "Recording token does not match this exam"}), 403

        part_path = os.path.join(part_dir, f"{seq:08d}.part")
        if not os.path.isfile(part_path):
            with open(part_path, "wb") as out_file:
                shutil.copyfileobj(video.stream, out_file, length=1024 * 1024)
        meta["updated_at"] = _now_local().isoformat(timespec="seconds")
        _save_recording_meta(part_dir, meta)

        # Pass this chunk on to the admin server right away (background).
        try:
            fwd_dir = os.path.join(FWD_FOLDER, token)
            os.makedirs(fwd_dir, exist_ok=True)
            fwd_path = os.path.join(fwd_dir, f"{seq:08d}.part")
            if not os.path.isfile(fwd_path) and os.path.isfile(part_path):
                shutil.copyfile(part_path, fwd_path)
            if os.path.isfile(fwd_path):
                with FWD_STATE_LOCK:
                    st = FWD_STATE.setdefault(token, {"queued": set(), "sent": set()})
                    first_time = seq not in st["queued"]
                    st["queued"].add(seq)
                if first_time:
                    _queue_recording_chunk_for_admin(
                        fwd_path, exam_id, session.get("student_id", ""),
                        meta.get("filename", ""), token, seq)
        except Exception as fwd_exc:
            print("[SYNC] chunk forward skipped:", fwd_exc)

        # FIX (real bug — root cause of "sometimes corrupted"): this
        # used to also push every individual chunk to the admin server
        # over the network, where the admin independently reconstructed
        # its own copy of the video as chunks trickled in. That was a
        # SECOND, separate, more fragile assembly of the same recording
        # racing against the single reliable one below (the complete,
        # already-verified file assembled locally and pushed as one
        # piece once the exam ends) — if the admin's own reconstruction
        # happened to finish first and any one chunk-push over the
        # network had failed, admin was left with a corrupted video, and
        # depending on timing that could win the race against the good
        # copy. There is now exactly one path that ever produces the
        # admin's copy: the verified local file, once assembled — see
        # finalize_exam_recording / _background_finalize_recording.
        return jsonify({
            "success": True,
            "filename": meta.get("filename", ""),
            "sequence": seq,
        })
    except Exception as e:
        print("Recording Chunk Upload Error:", str(e))
        return jsonify({"success": False, "error": str(e)}), 500


@app.route("/student/exam/<exam_id>/finalize-recording", methods=["POST"])
@student_login_required
def finalize_exam_recording(exam_id):
    try:
        token = str(request.form.get("recording_token", "")).strip()
        expected_raw = str(request.form.get("expected_last_seq", "")).strip()
        expected = int(expected_raw) if expected_raw.isdigit() else None
        if not token or not re.fullmatch(r"[A-Za-z0-9_-]{16,80}", token):
            return jsonify({"success": False, "error": "Invalid recording token"}), 400
        part_dir = os.path.join(RECORDINGS_FOLDER, ".examguard_parts", token)
        if not os.path.isdir(part_dir):
            return jsonify({"success": False, "error": "No recording parts found"}), 404
        meta = _load_recording_meta(part_dir)
        if not meta:
            return jsonify({"success": False, "error": "Recording metadata is missing"}), 404
        if str(meta.get("student_id", "")) != str(session.get("student_id", "")) or str(meta.get("exam_id", "")) != str(exam_id):
            return jsonify({"success": False, "error": "Recording token does not match this exam"}), 403
        next_seq, partial = _assemble_ready_recording_parts(part_dir, meta)
        if expected is not None and next_seq <= expected:
            return jsonify({"success": False, "retry": True, "missing_sequences": list(range(next_seq, min(expected+1,next_seq+41))), "next_seq": next_seq}), 409
        filename=os.path.basename(str(meta.get("filename","")).strip())
        if not filename or not os.path.isfile(partial) or os.path.getsize(partial)==0:
            return jsonify({"success":False,"error":"Recording data is empty"}),404
        # FIX: validate the assembled file BEFORE trusting it as the
        # finished recording — a corrupt/truncated assembly (e.g. from
        # a chunk that failed to fully write to local disk) must never
        # become "the" recording for this exam attempt, and must never
        # get pushed to admin as if it were valid.
        if not _is_valid_local_webm(partial):
            return jsonify({"success": False, "error": "Assembled recording failed validation", "retry": True}), 409
        final_path=os.path.join(RECORDINGS_FOLDER,filename)
        if not os.path.isfile(final_path): os.replace(partial,final_path)
        try:
            for n in os.listdir(part_dir):
                try: os.remove(os.path.join(part_dir,n))
                except OSError: pass
            os.rmdir(part_dir)
        except OSError: pass
        # FIX: this used to also call _queue_recording_finalize_for_admin,
        # which told the admin server to reconstruct its OWN copy from
        # individually-pushed chunks. That pipeline no longer exists
        # (see upload_exam_recording_chunk) — the verified local file
        # below is now the one and only source of the admin's copy.
        _deliver_recording_to_admin(final_path, exam_id, session.get("student_id", ""), filename, token, expected)
        return jsonify({"success":True,"filename":filename})
    except Exception as e:
        print("Recording Finalize Error:",str(e))
        return jsonify({"success":False,"error":str(e)}),500




def _background_finalize_recording(exam_id, student_id, token, expected_last_seq, wait_seconds=45):
    """Finalize a continuously uploaded recording after result submission.

    Runs outside the submit request. It waits briefly for the last chunk(s);
    if some never arrive it still publishes everything that DID arrive in
    order (a slightly shorter video is far better than none).
    """
    try:
        _rec_status_set(student_id, exam_id, "assembling", "Assembling the video file.")
        part_dir = os.path.join(RECORDINGS_FOLDER, ".examguard_parts", token)
        deadline = time.time() + max(1, int(wait_seconds))

        def publish(meta, partial):
            filename = os.path.basename(str(meta.get("filename", "")).strip())
            if filename and _is_valid_local_webm(partial):
                final_path = os.path.join(RECORDINGS_FOLDER, filename)
                if not os.path.isfile(final_path):
                    os.replace(partial, final_path)
                try:
                    for n in os.listdir(part_dir):
                        try: os.remove(os.path.join(part_dir, n))
                        except OSError: pass
                    os.rmdir(part_dir)
                except OSError: pass
                print("Background recording finalized:", filename)
                _deliver_recording_to_admin(final_path, exam_id, student_id, filename, token, expected_last_seq)
                return True
            return False

        while time.time() < deadline:
            meta = _load_recording_meta(part_dir) if os.path.isdir(part_dir) else None
            if meta and str(meta.get("student_id", "")) == str(student_id) and str(meta.get("exam_id", "")) == str(exam_id):
                next_seq, partial = _assemble_ready_recording_parts(part_dir, meta)
                if expected_last_seq is None or next_seq > expected_last_seq:
                    if publish(meta, partial):
                        return True
            elif not os.path.isdir(part_dir):
                # Already finalized by the browser's own finalize call.
                st = _rec_status_get(student_id, exam_id)
                if st.get("state") in ("uploading", "done"):
                    return True
            time.sleep(0.25)

        meta = _load_recording_meta(part_dir) if os.path.isdir(part_dir) else None
        if meta and str(meta.get("student_id", "")) == str(student_id) and str(meta.get("exam_id", "")) == str(exam_id):
            next_seq, partial = _assemble_ready_recording_parts(part_dir, meta)
            if next_seq > 0 and publish(meta, partial):
                print("Background recording finalized with partial data:", token)
                return True
        st = _rec_status_get(student_id, exam_id)
        if st.get("state") not in ("uploading", "done"):
            _rec_status_set(student_id, exam_id, "failed", "The recording could not be assembled.")
        print("Background recording finalize timed out:", token)
    except Exception as e:
        _rec_status_set(student_id, exam_id, "failed", "Recording processing error.")
        print("Background recording finalize error:", str(e))
    return False

@app.route("/student/exam/<exam_id>/upload-recording", methods=["POST"])
@student_login_required
def upload_exam_recording(exam_id):
    """Primary final-recording upload.

    The browser sends the complete MediaRecorder Blob after the recorder has
    stopped.  This is intentionally independent of the rolling chunk/assembly
    path so a late/missing chunk cannot prevent the final .webm from being
    created.  The existing chunk pipeline remains as a backup.
    """
    temp_path = None
    try:
        if "video" not in request.files:
            return jsonify({"success": False, "error": "No recording received"}), 400

        video = request.files["video"]
        if not video or not video.filename:
            return jsonify({"success": False, "error": "Empty recording"}), 400

        token = str(request.form.get("recording_token","")).strip()
        if token and not re.fullmatch(r"[A-Za-z0-9_-]{16,80}", token):
            token = ""

        safe_student = "".join(
            c for c in str(session.get("student_id", "student"))
            if c.isalnum() or c in "-_"
        ) or "student"
        safe_exam = "".join(
            c for c in str(exam_id)
            if c.isalnum() or c in "-_"
        ) or "exam"

        filename = ""
        if token:
            part_dir = os.path.join(RECORDINGS_FOLDER, ".examguard_parts", token)
            meta = _load_recording_meta(part_dir) if os.path.isdir(part_dir) else None
            if meta and str(meta.get("student_id", "")) == str(session.get("student_id", "")) and str(meta.get("exam_id", "")) == str(exam_id):
                # FIX (real bug — this was the main cause of duplicate
                # recordings): _safe_recording_component() strips every
                # character that isn't alphanumeric/'-'/'_', which also
                # strips the "." out of an already-safe filename like
                # "alice_EX1_..._ab12cd34.webm". That turned it into
                # "..._ab12cd34webm", which then no longer ends in
                # ".webm", so ".webm" got appended AGAIN — producing a
                # different filename ("..._ab12cd34webm.webm") than the
                # one the chunk-recording pipeline was already using
                # for this exact exam attempt. Two different filenames
                # for the same recording is exactly how it ended up
                # stored more than once. meta["filename"] was already
                # generated safely by this same app, so it only needs
                # a basename() for defense-in-depth here, not character
                # stripping that can corrupt a valid extension.
                candidate = os.path.basename(str(meta.get("filename", "")).strip())
                if candidate and re.fullmatch(r"[A-Za-z0-9._-]+", candidate):
                    filename = candidate
                    if not filename.lower().endswith(".webm"):
                        filename += ".webm"
        if not filename:
            # FIX: made this consistent with the chunk pipeline's naming
            # (student+exam only, no per-token/timestamp suffix) so
            # that regardless of which code path names this recording
            # first, every one of them converges on the exact same
            # filename — the true fix for duplicate/competing copies.
            filename = f"{safe_student}_{safe_exam}.webm"
        filepath = os.path.join(RECORDINGS_FOLDER, filename)
        # Use a per-request-unique temp name (not just filepath + ".uploading")
        # so that if two attempts for the same deterministic filename ever
        # overlap in time, they can't corrupt each other's partial write —
        # only the final os.replace() (atomic) decides what ends up at
        # `filepath`.
        temp_path = filepath + f".{uuid.uuid4().hex[:8]}.uploading"

        video.save(temp_path)
        size = os.path.getsize(temp_path)
        if size < 1024:
            raise ValueError("Recording file is empty or too small")

        # WebM/EBML files begin with the EBML magic bytes 1A 45 DF A3.
        with open(temp_path, "rb") as fh:
            magic = fh.read(4)
        if magic != bytes((0x1A, 0x45, 0xDF, 0xA3)):
            raise ValueError("Uploaded recording is not a valid WebM file")

        os.replace(temp_path, filepath)
        temp_path = None
        print(f"[RECORDING] Final recording saved: {filename} ({size} bytes)")

        # On a separate admin machine this queues a durable Student -> Admin
        # transfer. On the same machine the file is already in the shared
        # project recordings folder, so Admin can see it immediately.
        _queue_recording_for_admin(
            filepath,
            exam_id,
            session.get("student_id", ""),
            filename,
        )

        return jsonify({
            "success": True,
            "filename": filename,
            "size": size,
        })

    except Exception as e:
        if temp_path:
            try:
                os.remove(temp_path)
            except OSError:
                pass
        print("Recording Upload Error:", str(e))
        return jsonify({"success": False, "error": str(e)}), 500


# ============================================================
# LIVE AUDIO FOR ADMIN MONITORING
# Receives a short rolling audio clip every ~2.2 seconds and
# overwrites the previous one — the admin app polls and plays
# whatever is currently saved here, giving near-live sound
# without needing WebRTC/WebSocket infrastructure.
# ============================================================

@app.route("/student/exam/live-audio-chunk", methods=["POST"])
@student_login_required
def live_audio_chunk():

    try:

        audio_file = request.files.get("audio")

        if not audio_file:
            return jsonify({
                "success": False,
                "error": "No audio received"
            })

        student_id = session.get("student_id", "unknown")

        safe_id = "".join(
            c for c in str(student_id)
            if c.isalnum() or c in "-_"
        )

        os.makedirs(LIVE_FRAMES_FOLDER, exist_ok=True)

        filepath = os.path.join(LIVE_FRAMES_FOLDER, f"{safe_id}_audio.webm")

        audio_file.save(filepath)
        if os.path.isfile(filepath):
            threading.Thread(target=_post_live_audio_to_admin,args=(filepath,student_id),daemon=True).start()

        return jsonify({"success": True})

    except Exception as e:

        print("Live Audio Chunk Error:", str(e))

        return jsonify({
            "success": False,
            "error": str(e)
        }), 500


# ============================================================
# ADMIN RECORDINGS PAGE / DOWNLOAD
# ============================================================



def _local_lan_ip():
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.connect(("192.168.1.1", 80))
        ip = sock.getsockname()[0]
        sock.close()
        return ip
    except Exception:
        try:
            return socket.gethostbyname(socket.gethostname())
        except Exception:
            return "127.0.0.1"


@app.route("/student/exam/live-frame", methods=["POST"])
@student_login_required
def student_live_frame():
    """Store and relay the student's newest camera snapshot.

    This endpoint is deliberately separate from /monitor: displaying the
    camera must never wait for MediaPipe/AI processing. Only the newest JPEG
    is retained, so slow networks cannot build a queue of old frames.
    """
    temp_path = None
    try:
        data = request.get_json(silent=True) or {}
        exam_id = str(data.get("exam_id", session.get("current_exam_id", ""))).strip()
        if not exam_id or exam_id != str(session.get("current_exam_id", "")):
            return jsonify({"success": False, "error": "Invalid exam"}), 403
        image_data = data.get("image", "")
        if not image_data:
            return jsonify({"success": False, "error": "No image received"}), 400
        if "," in image_data:
            image_data = image_data.split(",", 1)[1]
        image_bytes = base64.b64decode(image_data, validate=True)
        np_array = np.frombuffer(image_bytes, np.uint8)
        frame = cv2.imdecode(np_array, cv2.IMREAD_COLOR)
        if frame is None:
            return jsonify({"success": False, "error": "Invalid image"}), 400

        student_id = str(session.get("student_id", "unknown"))
        safe_id = _safe_live_sync_id(student_id)
        os.makedirs(LIVE_FRAMES_FOLDER, exist_ok=True)
        frame_path = os.path.join(LIVE_FRAMES_FOLDER, f"{safe_id}.jpg")
        temp_path = frame_path + f".{uuid.uuid4().hex[:8]}.uploading"
        _ok_jpg, _jpg_buf = cv2.imencode(".jpg", frame, [cv2.IMWRITE_JPEG_QUALITY, 60])
        if not _ok_jpg:
            raise IOError("Could not encode live JPEG")
        with open(temp_path, "wb") as _jpg_fh:
            _jpg_fh.write(_jpg_buf.tobytes())

        # Atomic replacement means admin never reads a half-written JPEG.
        os.replace(temp_path, frame_path)
        temp_path = None

        # Use the newest AI result for the card status, if one exists.
        stats = {}
        monitor_key = _monitor_key(student_id, exam_id)
        try:
            state = _get_monitor_state(monitor_key)
            with state["lock"]:
                stats = dict(state.get("latest_stats", {}))
        except Exception:
            stats = {}

        live_payload = {
            "student_id": student_id,
            "student_name": session.get("student_name", ""),
            "exam_id": exam_id,
            "last_seen": time.time(),
            "status": stats.get("status", "Monitoring"),
            "warning": bool(stats.get("warning", False)),
            "warning_message": stats.get("warning_message", ""),
            "student_signal_base_url": _student_public_signal_base_url(),
            **_live_violation_fields(student_id),
        }
        status_path = os.path.join(LIVE_FRAMES_FOLDER, f"{safe_id}.json")
        status_tmp = status_path + ".uploading"
        with open(status_tmp, "w", encoding="utf-8") as fh:
            json.dump(live_payload, fh)
        os.replace(status_tmp, status_path)

        _schedule_live_frame_sync(frame_path, student_id, live_payload)
        return jsonify({"success": True, "timestamp": live_payload["last_seen"]})
    except (ValueError, base64.binascii.Error) as exc:
        return jsonify({"success": False, "error": f"Invalid live frame: {exc}"}), 400
    except Exception as exc:
        print("Live frame endpoint error:", exc)
        return jsonify({"success": False, "error": str(exc)}), 500
    finally:
        if temp_path and os.path.exists(temp_path):
            try:
                os.remove(temp_path)
            except OSError:
                pass


@app.route("/internal/live-frame/<student_id>")
def internal_live_frame(student_id):
    """Token-protected latest frame for direct admin pull on a LAN."""
    if not LIVE_SYNC_TOKEN or request.headers.get("X-ExamGuard-Sync-Token", "") != LIVE_SYNC_TOKEN:
        return jsonify({"success": False, "error": "Unauthorized"}), 401
    sid = str(student_id).strip()
    safe_id = _safe_live_sync_id(sid)
    path = os.path.join(LIVE_FRAMES_FOLDER, f"{safe_id}.jpg")
    if not os.path.isfile(path):
        return "", 404
    response = send_from_directory(LIVE_FRAMES_FOLDER, f"{safe_id}.jpg", mimetype="image/jpeg")
    response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    return response


@app.route("/student/exam/live-presence", methods=["POST"])
@student_login_required
def live_presence():
    try:
        data = request.get_json(silent=True) or {}
        exam_id = str(data.get("exam_id", session.get("current_exam_id", ""))).strip()
        if not exam_id or exam_id != str(session.get("current_exam_id", "")):
            return jsonify({"success": False, "error": "Invalid exam"}), 403
        sid = str(session.get("student_id", ""))
        payload = {
            "student_id": sid,
            "student_name": str(session.get("student_name", "")),
            "exam_id": exam_id,
            "last_seen": time.time(),
            "status": "Live",
            "warning": False,
            "warning_message": "",
            "student_signal_base_url": _student_public_signal_base_url(),
            **_live_violation_fields(sid),
        }
        _schedule_live_heartbeat_sync(sid, payload)
        return jsonify({"success": True})
    except Exception as exc:
        print("Live presence error:", exc)
        return jsonify({"success": False, "error": str(exc)}), 500


@app.route("/student/exam/monitor", methods=["POST"])
@student_login_required
def monitor_exam():

    try:

        data = request.get_json()


        if not data or "image" not in data:

            return jsonify({
                "success": False,
                "error": "No image received"
            })


        image_data = data["image"]


        # Remove base64 header
        if "," in image_data:

            image_data = image_data.split(
                ",",
                1
            )[1]


        image_bytes = base64.b64decode(
            image_data
        )


        np_array = np.frombuffer(
            image_bytes,
            np.uint8
        )


        frame = cv2.imdecode(
            np_array,
            cv2.IMREAD_COLOR
        )


        if frame is None:

            return jsonify({
                "success": False,
                "error": "Invalid image"
            })


        # FIX: analyze_face_frame now needs to know WHICH student
        # this frame belongs to, so it can use that student's own
        # isolated tracking state/FaceMesh instance instead of one
        # shared across everybody currently taking an exam.
        monitor_key = _monitor_key(
            session.get("student_id", "unknown"),
            session.get("current_exam_id", "")
        )

        stats = analyze_face_frame(
            frame, monitor_key
        )

        # Live camera display is intentionally handled by the separate
        # /student/exam/live-frame endpoint. Keeping it out of this AI
        # request is critical: MediaPipe analysis must never block or delay
        # the newest camera frame sent to the admin page.

        return jsonify({

            "success": True,

            "stats": stats

        })


    except Exception as e:

        print(
            "Monitoring Error:",
            str(e)
        )


        return jsonify({

            "success": False,

            "error": str(e)
        })




# ============================================================
# REMOTE ADMIN -> STUDENT VOICE SIGNALING
# ============================================================

def _voice_cleanup():
    cutoff = time.time() - VOICE_SIGNAL_TTL_SECONDS
    with VOICE_SIGNAL_LOCK:
        stale = [sid for sid, item in VOICE_SIGNAL_STATE.items()
                 if item.get("updated_at", 0) < cutoff]
        for sid in stale:
            VOICE_SIGNAL_STATE.pop(sid, None)


def _voice_token_ok():
    return request.headers.get("X-Voice-Signal-Token", "") == VOICE_SIGNAL_TOKEN


# ============================================================
# REMOTE LIVE VIDEO SIGNALING
# ============================================================

def _video_cleanup():
    cutoff = time.time() - VIDEO_SIGNAL_TTL_SECONDS
    with VIDEO_SIGNAL_LOCK:
        stale = [sid for sid, item in VIDEO_SIGNAL_STATE.items()
                 if item.get("updated_at", 0) < cutoff]
        for sid in stale:
            VIDEO_SIGNAL_STATE.pop(sid, None)


def _video_token_ok():
    return request.headers.get("X-Video-Signal-Token", "") == VOICE_SIGNAL_TOKEN


@app.route("/internal/video/offer", methods=["POST"])
def internal_video_offer():
    if not _video_token_ok():
        return jsonify({"success": False, "error": "Unauthorized"}), 401
    _video_cleanup()
    data = request.get_json(silent=True) or {}
    student_id = str(data.get("student_id", "")).strip()
    exam_id = str(data.get("exam_id", "")).strip()
    offer = data.get("offer")
    if not student_id or not exam_id or not isinstance(offer, dict):
        return jsonify({"success": False, "error": "Invalid video offer"}), 400
    status_file = os.path.join(
        LIVE_FRAMES_FOLDER,
        f"{''.join(c for c in student_id if c.isalnum() or c in '-_')}.json"
    )
    try:
        with open(status_file, "r", encoding="utf-8") as f:
            status = json.load(f)
        if time.time() - float(status.get("last_seen", 0) or 0) > 10:
            return jsonify({"success": False, "error": "Student is not currently live"}), 409
        if str(status.get("exam_id", "")) != exam_id:
            return jsonify({"success": False, "error": "Exam mismatch"}), 409
    except Exception:
        return jsonify({"success": False, "error": "Student is not currently live"}), 409
    with VIDEO_SIGNAL_LOCK:
        VIDEO_SIGNAL_STATE[student_id] = {
            "exam_id": exam_id,
            "offer": offer,
            "answer": None,
            "updated_at": time.time(),
        }
    return jsonify({"success": True})


@app.route("/student/exam/video/poll")
@student_login_required
def student_video_poll():
    _video_cleanup()
    student_id = str(session.get("student_id", ""))
    exam_id = str(request.args.get("exam_id", ""))
    if not student_id or not exam_id or exam_id != str(session.get("current_exam_id", "")):
        return jsonify({"success": False, "offer": None}), 403
    with VIDEO_SIGNAL_LOCK:
        item = VIDEO_SIGNAL_STATE.get(student_id)
        if not item or item.get("exam_id") != exam_id:
            return jsonify({"success": True, "offer": None})
        return jsonify({"success": True, "offer": item.get("offer")})


@app.route("/student/exam/video/answer", methods=["POST"])
@student_login_required
def student_video_answer():
    data = request.get_json(silent=True) or {}
    student_id = str(session.get("student_id", ""))
    exam_id = str(data.get("exam_id", ""))
    answer = data.get("answer")
    if not exam_id or exam_id != str(session.get("current_exam_id", "")) or not isinstance(answer, dict):
        return jsonify({"success": False, "error": "Invalid video answer"}), 400
    with VIDEO_SIGNAL_LOCK:
        item = VIDEO_SIGNAL_STATE.get(student_id)
        if not item or item.get("exam_id") != exam_id:
            return jsonify({"success": False, "error": "No pending video session"}), 404
        item["answer"] = answer
        item["updated_at"] = time.time()
    return jsonify({"success": True})


@app.route("/internal/video/answer/<student_id>")
def internal_video_answer(student_id):
    if not _video_token_ok():
        return jsonify({"success": False, "error": "Unauthorized"}), 401
    _video_cleanup()
    safe_id = "".join(c for c in str(student_id) if c.isalnum() or c in "-_")
    with VIDEO_SIGNAL_LOCK:
        item = VIDEO_SIGNAL_STATE.get(safe_id)
        if not item or not item.get("answer"):
            return jsonify({"success": True, "answer": None})
        answer = item["answer"]
        item["answer"] = None
        item["updated_at"] = time.time()
        return jsonify({"success": True, "answer": answer})


@app.route("/internal/video/clear/<student_id>", methods=["POST"])
def internal_video_clear(student_id):
    if not _video_token_ok():
        return jsonify({"success": False, "error": "Unauthorized"}), 401
    safe_id = "".join(c for c in str(student_id) if c.isalnum() or c in "-_")
    with VIDEO_SIGNAL_LOCK:
        VIDEO_SIGNAL_STATE.pop(safe_id, None)
    return jsonify({"success": True})


@app.route("/internal/voice/offer", methods=["POST"])
def internal_voice_offer():
    """Receive an offer from admin_app.py for a currently active student."""
    if not _voice_token_ok():
        return jsonify({"success": False, "error": "Unauthorized"}), 401

    _voice_cleanup()
    data = request.get_json(silent=True) or {}
    student_id = str(data.get("student_id", "")).strip()
    exam_id = str(data.get("exam_id", "")).strip()
    offer = data.get("offer")

    if not student_id or not exam_id or not isinstance(offer, dict):
        return jsonify({"success": False, "error": "Invalid voice offer"}), 400

    # Admin may only offer to a student who is actually taking this exam.
    # The live-monitor JSON is the same heartbeat used by the admin monitor.
    status_file = os.path.join(LIVE_FRAMES_FOLDER, f"{''.join(c for c in student_id if c.isalnum() or c in '-_')}.json")
    active = False
    try:
        with open(status_file, "r") as f:
            status = json.load(f)
        active = (
            time.time() - status.get("last_seen", 0) <= 10
            and str(status.get("exam_id", "")) == exam_id
        )
    except Exception:
        pass

    if not active:
        return jsonify({"success": False, "error": "Student is not currently active in this exam"}), 409

    with VOICE_SIGNAL_LOCK:
        VOICE_SIGNAL_STATE[student_id] = {
            "exam_id": exam_id,
            "offer": offer,
            "answer": None,
            "updated_at": time.time(),
        }

    return jsonify({"success": True})


@app.route("/student/exam/voice/poll")
@student_login_required
def student_voice_poll():
    """Student browser polls for an admin offer."""
    _voice_cleanup()
    student_id = str(session.get("student_id", ""))
    exam_id = str(request.args.get("exam_id", ""))
    current_exam = str(session.get("current_exam_id", ""))

    if not student_id or not exam_id or exam_id != current_exam:
        return jsonify({"success": False, "offer": None}), 403

    with VOICE_SIGNAL_LOCK:
        item = VOICE_SIGNAL_STATE.get(student_id)
        if not item or item.get("exam_id") != exam_id:
            return jsonify({"success": True, "offer": None})
        return jsonify({"success": True, "offer": item.get("offer")})


@app.route("/student/exam/voice/answer", methods=["POST"])
@student_login_required
def student_voice_answer():
    data = request.get_json(silent=True) or {}
    student_id = str(session.get("student_id", ""))
    exam_id = str(data.get("exam_id", ""))
    answer = data.get("answer")

    if not exam_id or exam_id != str(session.get("current_exam_id", "")) or not isinstance(answer, dict):
        return jsonify({"success": False, "error": "Invalid voice answer"}), 400

    with VOICE_SIGNAL_LOCK:
        item = VOICE_SIGNAL_STATE.get(student_id)
        if not item or item.get("exam_id") != exam_id:
            return jsonify({"success": False, "error": "No pending voice session"}), 404
        item["answer"] = answer
        item["updated_at"] = time.time()

    return jsonify({"success": True})


@app.route("/internal/voice/answer/<student_id>")
def internal_voice_answer(student_id):
    """Admin server polls this to obtain a student's WebRTC answer."""
    if not _voice_token_ok():
        return jsonify({"success": False, "error": "Unauthorized"}), 401

    _voice_cleanup()
    safe_id = "".join(c for c in str(student_id) if c.isalnum() or c in "-_")
    with VOICE_SIGNAL_LOCK:
        item = VOICE_SIGNAL_STATE.get(safe_id)
        if not item or not item.get("answer"):
            return jsonify({"success": True, "answer": None})
        answer = item["answer"]
        # Keep the entry alive for the connected peer, but remove the answer
        # so the admin does not repeatedly apply the same SDP answer.
        item["answer"] = None
        item["updated_at"] = time.time()
        return jsonify({"success": True, "answer": answer})


@app.route("/internal/voice/clear/<student_id>", methods=["POST"])
def internal_voice_clear(student_id):
    if not _voice_token_ok():
        return jsonify({"success": False, "error": "Unauthorized"}), 401
    safe_id = "".join(c for c in str(student_id) if c.isalnum() or c in "-_")
    with VOICE_SIGNAL_LOCK:
        VOICE_SIGNAL_STATE.pop(safe_id, None)
    return jsonify({"success": True})


UNLOCK_FAILS = {}
UNLOCK_FAILS_LOCK = threading.Lock()
UNLOCK_MAX_WRONG = 5
UNLOCK_LOCKOUT_SECONDS = 30


def _unlock_letters():
    return re.sub(r"[^A-Za-z]", "", str(KEYBOARD_UNLOCK_PASSWORD or ""))


@app.route("/student/exam/<exam_id>/recording-status")
@student_login_required
def recording_status(exam_id):
    """Polled by the on-screen keyboard page while the video is being saved."""
    st = _rec_status_get(session.get("student_id", ""), exam_id)
    state = st.get("state", "none") if st else "none"
    return jsonify({
        "success": True,
        "state": state,
        "detail": st.get("detail", "") if st else "",
        "ready": _recording_ready(session.get("student_id", ""), exam_id),
    })


@app.route("/student/exam/keyboard-unlock", methods=["POST"])
@student_login_required
def keyboard_unlock():
    """Validate the unlock password typed on the ON-SCREEN keyboard.

    Letters only (case-insensitive), rate limited, and refused until the exam
    recording has been handed over so the unlock cannot cut it short.
    """
    data = request.get_json(silent=True) or {}
    exam_id = str(data.get("exam_id", "")).strip()
    raw_candidate = str(data.get("password", ""))
    candidate = raw_candidate

    allowed = {str(session.get("current_exam_id", "")), str(session.get("result_lock_exam_id", "")),
               str(session.get("kb_locked_exam", ""))}
    allowed.discard("")
    if not exam_id or exam_id not in allowed:
        return jsonify({"success": False, "unlocked": False, "error": "forbidden"}), 403

    student_id = str(session.get("student_id", ""))
    now = time.time()
    with UNLOCK_FAILS_LOCK:
        entry = UNLOCK_FAILS.get(student_id, {"count": 0, "until": 0.0})
        if entry["until"] > now:
            return jsonify({"success": False, "unlocked": False, "error": "rate_limited",
                            "retry_after": int(entry["until"] - now) + 1}), 429

    if not _recording_ready(student_id, exam_id):
        return jsonify({"success": True, "unlocked": False, "reason": "recording_pending"})

    real = _unlock_letters()
    ok = bool(real) and raw_candidate.isalpha() and raw_candidate.isascii() and candidate.lower() == real.lower()
    with UNLOCK_FAILS_LOCK:
        if ok:
            UNLOCK_FAILS.pop(student_id, None)
        else:
            entry = UNLOCK_FAILS.setdefault(student_id, {"count": 0, "until": 0.0})
            entry["count"] += 1
            if entry["count"] >= UNLOCK_MAX_WRONG:
                entry["count"] = 0
                entry["until"] = now + UNLOCK_LOCKOUT_SECONDS

    if ok:
        session.pop("result_lock_exam_id", None)
        session.pop("kb_locked", None)
        session.pop("kb_locked_exam", None)
    return jsonify({"success": True, "unlocked": ok})


@app.route("/student/exam/<exam_id>")
@student_login_required
def start_exam(exam_id):

    student_id = session.get("student_id", "")

    # =========================================================
    # BLOCK RE-ENTRY — once a student has any result recorded for
    # this exam (completed normally OR auto-submitted due to
    # violations), they cannot start it again.
    # =========================================================
    results_workbook = load_database()
    try:
        prior_attempts = _results_attempts(results_workbook, student_id)
    finally:
        results_workbook.close()

    prior_status = prior_attempts.get(str(exam_id).strip())
    if prior_status is not None:
        if prior_status != "Completed":
            flash(
                f"Your access to this exam was ended ({prior_status}). You cannot re-attempt it.",
                "error"
            )
        else:
            flash(
                "You have already completed this exam and cannot retake it.",
                "error"
            )
        return redirect(url_for("student_dashboard"))

    workbook = load_database()

    sheet = workbook["Exams"]

    questions = []

    subject_name = ""
    subject_code = ""
    teacher_name = ""
    available_from_raw = ""
    available_until_raw = ""
    duration_minutes = 30


    for row in sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        if row[0] == exam_id:

            subject_name = row[3]

            subject_code = row[4]

            teacher_name = row[2]

            if len(row) > 12 and row[12]:
                available_from_raw = row[12]

            if len(row) > 13 and row[13]:
                available_until_raw = row[13]

            if len(row) > 14 and row[14]:
                try:
                    duration_minutes = int(row[14])
                except (TypeError, ValueError):
                    duration_minutes = 30

            questions.append({

                "number": row[5],

                "question": row[6],

                "option_a": row[7],

                "option_b": row[8],

                "option_c": row[9],

                "option_d": row[10],

                "correct_answer": row[11]

            })


    workbook.close()


    if not questions:

        flash(
            "Exam not found.",
            "error"
        )

        return redirect(
            url_for("student_dashboard")
        )

    # =========================================================
    # AVAILABILITY WINDOW — only enforced if the teacher set one
    # =========================================================
    now = _now_local()

    def _to_datetime(raw_value):
        """
        FIX: openpyxl can hand back a value that is ALREADY a Python
        datetime object instead of a string — this happens whenever
        Excel/openpyxl decides a cell "looks like" a date (which is
        common once a date-like string has been written+reopened in
        Excel, or if a teacher opens database.xlsx and re-saves it).
        datetime.strptime() requires a string, so passing it a
        datetime object raised an unhandled TypeError — NOT a
        ValueError — which the old code didn't catch, so Flask threw
        a raw 500 error that looked like "invalid date" to the user
        even though the date the teacher entered was perfectly valid.
        This helper accepts either a string OR a datetime and always
        returns a datetime (or None if it truly can't be parsed).
        """
        if isinstance(raw_value, datetime):
            return raw_value

        if not isinstance(raw_value, str) or not raw_value.strip():
            return None

        raw_value = raw_value.strip()

        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%dT%H:%M"):
            try:
                return datetime.strptime(raw_value, fmt)
            except ValueError:
                continue

        return None

    if available_from_raw:
        opens_at = _to_datetime(available_from_raw)
        if opens_at and now < opens_at:
            flash(
                f"This exam is not open yet. It becomes available at {opens_at.strftime('%d %b %Y, %I:%M %p')}.",
                "error"
            )
            return redirect(url_for("student_dashboard"))

    if available_until_raw:
        closes_at = _to_datetime(available_until_raw)
        if closes_at and now > closes_at:
            flash(
                f"This exam closed at {closes_at.strftime('%d %b %Y, %I:%M %p')} and can no longer be attempted.",
                "error"
            )
            return redirect(url_for("student_dashboard"))

    # Track which exam is currently active for this student —
    # used by monitor_exam() to tag live frames for the admin system
    session["current_exam_id"] = exam_id
    session["current_exam_duration_minutes"] = duration_minutes
    with LIVE_VIOLATION_LOCK:
        LIVE_VIOLATION_STATE.pop(str(student_id), None)

    begun_at = EXAM_BEGIN_TIMES.get(_rec_key(student_id, exam_id))
    if begun_at is not None:
        remaining = int(duration_minutes * 60 - (time.time() - begun_at))
        if remaining <= 0:
            _record_forfeit(student_id, session.get("student_name", ""), session.get("student_email", ""),
                            exam_id, "Time Expired — Auto Submitted")
            flash("Your exam time is over. The attempt has been closed.", "error")
            return redirect(url_for("student_dashboard"))
        session["current_exam_remaining_seconds"] = remaining
    else:
        session["current_exam_remaining_seconds"] = duration_minutes * 60

    return render_template(

        "student_exam.html",

        exam_id=exam_id,

        subject_name=subject_name,

        subject_code=subject_code,

        teacher_name=teacher_name,

        questions=questions,

        duration_minutes=duration_minutes

    )




@app.route(
    "/student/exam/violation",
    methods=["POST"]
)
@student_login_required
def exam_violation():

    try:

        data = request.get_json()

        if not data:

            return jsonify({
                "success": False,
                "error": "No data received"
            })


        violation_type = data.get(
            "type",
            "unknown"
        )


        timestamp = data.get(
            "timestamp",
            ""
        )

        message = data.get("message", "")

        exam_id = data.get("exam_id", "")


        print(
            "EXAM VIOLATION:",
            violation_type,
            timestamp,
            message
        )

        log_violation_to_sheet(
            session.get("student_id", ""),
            exam_id,
            violation_type,
            message
        )
        _note_violation(session.get("student_id", ""), exam_id, violation_type, message)


        return jsonify({

            "success": True,

            "type": violation_type,

            "message":
                "Violation recorded."

        })


    except Exception as e:

        print(
            "Violation Error:",
            str(e)
        )


        return jsonify({

            "success": False,

            "error": str(e)

        })




@app.route("/student/exam/preflight-config")
@student_login_required
def preflight_config():
    """Settings for the pre-exam microphone / volume check popup."""
    return jsonify({
        "require_volume": os.environ.get("EXAMGUARD_REQUIRE_VOLUME_CHECK", "1").strip().lower() not in ("0", "false", "no", "off"),
        "min_tone_db": float(os.environ.get("EXAMGUARD_VOLUME_MIN_DB", "-40")),
    })


@app.route("/student/exam/audio-warning", methods=["POST"])
@student_login_required
def audio_warning_event():
    try:
        data=request.get_json(silent=True) or {}
        exam_id=str(data.get("exam_id",session.get("current_exam_id",""))).strip()
        level=float(data.get("audio_level",0) or 0)
        baseline=float(data.get("baseline",0) or 0)
        log_violation_to_sheet(session.get("student_id",""),exam_id,"audio_detected",f"Sustained microphone audio detected (level {level:.4f}, baseline {baseline:.4f})")
        return jsonify({"success":True,"warning":True,"warning_message":"🔊 Audio detected. Please remain silent during the examination."})
    except Exception as e:
        print("Audio Warning Event Error:",e)
        return jsonify({"success":False,"error":str(e)}),500


@app.route("/student/exam/audio-monitor",methods=["POST"])
@student_login_required
def audio_monitor():
    # Compatibility only. New clients perform detection locally and use /audio-warning.
    try:
        data=request.get_json(silent=True) or {}
        return jsonify({"success":True,"audio_level":float(data.get("audio_level",0) or 0),"audio_detected":False,"warning":False,"warning_message":""})
    except Exception as e:
        return jsonify({"success":False,"error":str(e)}),500


@app.route('/tab_violation', methods=['POST'])
def tab_violation():

    data = request.get_json()

    violation_count = data.get(
        'violation_count',
        0
    )

    message = data.get(
        'message',
        'Tab switching detected'
    )

    exam_id = data.get('exam_id', '')

    print(
        f"TAB VIOLATION {violation_count}: {message}"
    )

    log_violation_to_sheet(
        session.get("student_id", ""),
        exam_id,
        "tab_switch",
        f"{message} (count: {violation_count})"
    )
    _note_violation(session.get("student_id", ""), exam_id, "tab_switch_autoend", message)

    return jsonify({
        "success": True,
        "violation_count": violation_count
    })


# ============================================================
# AUTOMATIC EXAM CAMERA PREVIEW + VIDEO RECORDING
# ============================================================



EXAM_RECORDING_SCRIPT = r"""
<style>
#ai-camera-preview{
    position:fixed;right:18px;bottom:18px;width:190px;height:145px;
    background:#000;border:2px solid #fff;border-radius:10px;
    overflow:hidden;z-index:2147483000;box-shadow:0 4px 18px rgba(0,0,0,.35);
    transition:border-color .2s;
}
#ai-camera-preview.warn{border-color:#f87171}
#ai-camera-preview video{width:100%;height:100%;object-fit:cover;display:block}
#ai-camera-title{position:absolute;top:0;left:0;right:0;background:rgba(0,0,0,.65);
    color:#fff;text-align:center;font:12px Arial;padding:4px;z-index:2}
#ai-recording-status{position:absolute;bottom:4px;left:6px;background:rgba(0,0,0,.65);
    color:#fff;padding:3px 6px;border-radius:4px;font:11px Arial;z-index:2}

#ai-warning-banner{
    position:fixed;top:16px;left:50%;transform:translateX(-50%);
    background:#2c1616;border:1px solid #f87171;color:#fecaca;
    padding:10px 22px;border-radius:8px;font:600 13.5px 'Segoe UI',Arial,sans-serif;
    z-index:2147483400;display:none;max-width:80vw;text-align:center;
}
#ai-status-pill{
    position:fixed;left:18px;bottom:18px;z-index:2147483000;
    background:#14291e;color:#4ade80;border:1px solid #245c3a;
    padding:6px 14px;border-radius:20px;font:600 12.5px 'Segoe UI',Arial,sans-serif;
}
#ai-status-pill.warn{background:#2c1616;color:#f87171;border-color:#5c2a2a}
</style>
<div id="ai-camera-preview">
  <div id="ai-camera-title">Live Monitoring</div>
  <video id="ai-student-camera" autoplay playsinline muted></video>
  <div id="ai-recording-status">Starting camera...</div>
</div>
<div id="ai-status-pill">Monitoring Active</div>
<div id="ai-warning-banner"></div>
<canvas id="ai-capture-canvas" width="480" height="360" style="display:none"></canvas>

<script>
(() => {
  const examId = decodeURIComponent(location.pathname.split('/').filter(Boolean).pop());
  const ICE_SERVERS = __ICE_SERVERS_JSON__;
  const EXAM_DURATION_MIN = __EXAM_DURATION_MIN__;
  let stream = null;
  let recorder = null;
  let chunks = [];
  let submitting = false;
  let uploadedFile = '';
  let recordingToken = '';
  let recordingSeq = 0;
  const recordingBlobStore = new Map();
  const pendingRecordingUploads = new Map();
  const nativeSubmit = HTMLFormElement.prototype.submit;
  const video = document.getElementById('ai-student-camera');
  const canvas = document.getElementById('ai-capture-canvas');
  const ctx = canvas.getContext('2d');
  const preview = document.getElementById('ai-camera-preview');
  const statusPill = document.getElementById('ai-status-pill');
  const warningBanner = document.getElementById('ai-warning-banner');
  const status = msg => { const el=document.getElementById('ai-recording-status'); if(el) el.textContent=msg; };

  function getExamForm(){ return Array.from(document.forms).find(f=>(f.action||'').includes('/student/exam/')&&(f.action||'').includes('/submit')) || document.forms[0]; }
  function addHiddenField(form,name='recording_file'){
    let input=form.querySelector(`input[name="${name}"]`);
    if(!input){input=document.createElement('input');input.type='hidden';input.name=name;form.appendChild(input);} return input;
  }
  function makeRecordingToken(){try{if(window.crypto?.randomUUID)return crypto.randomUUID().replace(/-/g,'');}catch(e){}return ('rg'+Date.now().toString(36)+Math.random().toString(36).slice(2)).replace(/[^A-Za-z0-9_-]/g,'');}
  async function fetchWithTimeout(url,options,ms=2500){const c=new AbortController(),t=setTimeout(()=>c.abort(),ms);try{return await fetch(url,{...options,signal:c.signal});}finally{clearTimeout(t);}}
  const sleep = ms => new Promise(r=>setTimeout(r,ms));
  let uploadPumpRunning = false;
  let uploadGiveUp = false;
  let uploadFailStreak = 0;

  async function sendRecordingPart(blob,seq,attempts=3){
    if(!blob||!blob.size){recordingBlobStore.delete(Number(seq));return true;}
    for(let a=1;a<=attempts;a++){
      try{
        const fd=new FormData();fd.append('video',blob,`chunk_${seq}.webm`);
        const r=await fetchWithTimeout(`/student/exam/${encodeURIComponent(examId)}/upload-recording-chunk`,{method:'POST',body:fd,credentials:'same-origin',headers:{'X-Recording-Token':recordingToken,'X-Recording-Seq':String(seq)}},25000);
        const d=await r.json().catch(()=>({}));
        if(r.ok&&d.success){if(d.filename)uploadedFile=d.filename;recordingBlobStore.delete(Number(seq));return true;}
      }catch(e){console.warn('Recording upload',seq,a,e);}
      await sleep(Math.min(2500,a*600));
    }
    return false;
  }
  // Up to 3 parts upload at the same time (the server puts them back in
  // order by sequence number), so the backlog at the end of the exam is tiny.
  const inFlightParts=new Set();
  function pumpUploads(){
    if(uploadGiveUp)return;
    while(inFlightParts.size<3){
      const next=Array.from(recordingBlobStore.keys()).filter(k=>!inFlightParts.has(k)).sort((x,y)=>x-y)[0];
      if(next===undefined)break;
      inFlightParts.add(next);
      sendRecordingPart(recordingBlobStore.get(next),next,3).then(ok=>{
        uploadFailStreak=ok?0:uploadFailStreak+1;
        inFlightParts.delete(next);
        if(recordingBlobStore.size&&!uploadGiveUp)setTimeout(pumpUploads,ok?0:Math.min(8000,1000*uploadFailStreak));
      }).catch(()=>{inFlightParts.delete(next);setTimeout(pumpUploads,1500);});
    }
  }
  function queueRecordingPart(blob){
    const seq=recordingSeq++; recordingBlobStore.set(seq,blob); pumpUploads();
  }
  async function waitForRecordingUploads(ms=3000){
    const end=Date.now()+ms; pumpUploads();
    while(recordingBlobStore.size&&Date.now()<end){await sleep(150);}
    return recordingBlobStore.size===0;
  }
  function retryMissing(seq){ pumpUploads(); return Promise.resolve(); }
  async function finalizeRecording(){
    if(!recordingToken||recordingSeq===0)return '';
    const expected=recordingSeq-1;
    for(let attempt=1;attempt<=4;attempt++){
      const fd=new FormData();fd.append('recording_token',recordingToken);fd.append('expected_last_seq',String(expected));
      try{
        const r=await fetchWithTimeout(`/student/exam/${encodeURIComponent(examId)}/finalize-recording`,{method:'POST',body:fd,credentials:'same-origin'},15000);
        const d=await r.json().catch(()=>({}));
        if(r.ok&&d.success){uploadedFile=d.filename||uploadedFile||'';return uploadedFile;}
        if(d.retry&&Array.isArray(d.missing_sequences)){await retryMissing(); await waitForRecordingUploads(4000); continue;}
      }catch(e){console.warn('Recording finalize retry',attempt,e);}
      await sleep(500*attempt);
    }
    return '';
  }

  async function stopAndSubmit(form){
    if(submitting)return; submitting=true;
    const hidden=addHiddenField(form,'recording_file');
    const tokenInput=addHiddenField(form,'recording_token');
    const seqInput=addHiddenField(form,'recording_expected_last_seq');
    if(window.__aiStopMonitoring)window.__aiStopMonitoring(); if(window.__aiStopAudioMonitoring)window.__aiStopAudioMonitoring(); if(window.__aiStopAdminVoice)window.__aiStopAdminVoice(); if(window.__aiStopLiveVideo)window.__aiStopLiveVideo();

    // Show progress so the student never sees a frozen page.
    const ov=document.getElementById('ai-fs-ending-overlay');
    const ovTitle=document.getElementById('ai-fs-ending-title');
    const ovMsg=document.getElementById('ai-fs-ending-msg');
    if(ov) ov.style.display='flex';
    if(ovTitle) ovTitle.textContent='Saving your exam';
    const say=t=>{ if(ovMsg) ovMsg.textContent=t; status(t); };
    say('Saving your exam video...');
    const progress=setInterval(()=>{ const n=recordingBlobStore.size; say(n?`Saving your exam video... (${n} part${n>1?'s':''} left)`:'Finishing up...'); },700);

    // Stop MediaRecorder so its final dataavailable chunk is queued.
    try{
      if(recorder&&recorder.state!=='inactive')await Promise.race([
        new Promise(resolve=>{recorder.addEventListener('stop',resolve,{once:true});try{recorder.requestData();}catch(e){}recorder.stop();}),
        sleep(4000)
      ]);
    }catch(e){console.error('Recorder stop failed:',e);}

    // Upload the remaining chunks (in order) then ask the server to assemble.
    // Hard cap: after that the server-side finalizer salvages what arrived.
    try{
      await Promise.race([
        (async()=>{ await waitForRecordingUploads(28000); if(recordingToken) await finalizeRecording(); })(),
        sleep(36000)
      ]);
    }catch(e){console.warn('Recording finalize deferred to background:',e);}
    uploadGiveUp=true; clearInterval(progress);

    hidden.value=uploadedFile||'';
    tokenInput.value=recordingToken||'';
    seqInput.value=String(Math.max(0, recordingSeq - 1));
    if(stream)stream.getTracks().forEach(t=>t.stop());
    window.__aiAllowUnload=true;
    say('Submitting exam...');
    nativeSubmit.call(form);
  }

  // ===================== AI FACE / EYE / HEAD MONITORING =====================
  // Sends a webcam frame to the server every 1.5s for AI analysis.
  // Live camera display is handled independently by startLiveFrameLoop()
  // so the admin preview is not blocked by MediaPipe.
  let monitorTimer = null;
  let monitorInFlight = false;
  let monitorFailStreak = 0;
  let monitorOkAt = Date.now();
  function noteMonitorHealth(ok){
    monitorFailStreak = ok ? 0 : monitorFailStreak + 1;
    const offline = monitorFailStreak >= 5;
    if (offline) {
      statusPill.textContent = 'AI check reconnecting...';
      statusPill.classList.add('warn');
    } else if (ok && statusPill.textContent === 'AI check reconnecting...') {
      statusPill.textContent = 'Monitoring Active';
      statusPill.classList.remove('warn');
    }
    if (monitorFailStreak === 5) {
      // Tell the server once so the problem is visible in the logs / admin view.
      try { fetch('/student/exam/violation', {method:'POST', credentials:'same-origin', keepalive:true,
        headers:{'Content-Type':'application/json'},
        body: JSON.stringify({type:'monitor_offline', message:'AI face monitoring is not responding', exam_id: examId, timestamp: new Date().toISOString()})}).catch(()=>{}); } catch(e) {}
    }
  }

  function startMonitoringLoop(){
    monitorTimer = setInterval(async () => {
      if (submitting || !video.videoWidth || monitorInFlight) return;
      monitorInFlight = true;

      try {
        ctx.drawImage(video, 0, 0, canvas.width, canvas.height);
        const imageData = canvas.toDataURL('image/jpeg', 0.7);

        const res = await fetchWithTimeout('/student/exam/monitor', {
          method: 'POST',
          headers: {'Content-Type': 'application/json'},
          credentials: 'same-origin',
          body: JSON.stringify({image: imageData, exam_id: examId})
        }, 9000);
        const data = await res.json();
        if (data.success) { updateStats(data.stats); noteMonitorHealth(true); }
        else { console.error('Monitoring rejected:', data.error); noteMonitorHealth(false); }
      } catch (e) {
        console.error('Monitoring error:', e);
        noteMonitorHealth(false);
      } finally {
        monitorInFlight = false;
      }
    }, 1000);
  }

  window.__aiStopMonitoring = () => {
    if (monitorTimer) clearInterval(monitorTimer);
  };

  // Face/eye/head warnings and audio warnings are tracked separately
  // and combined, so one source's "all clear" doesn't wipe out the
  // other source's active warning.
  // FIX: the displayed message used to always prefer the face
  // warning whenever both were active at once ("faceWarningActive ?
  // faceWarningMsg : audioWarningMsg") — so a genuine audio warning
  // (e.g. talking detected) got silently hidden behind a lingering
  // "Face not detected" message any time both fired together. Now
  // each source's own activation time is tracked and whichever one
  // most recently turned on is shown.
  let faceWarningActive = false;
  let faceWarningMsg = '';
  let faceWarningSince = 0;
  let audioWarningActive = false;
  let audioWarningMsg = '';
  let audioWarningSince = 0;

  function refreshWarningUI(){
    const active = faceWarningActive || audioWarningActive;
    let message = '';
    if (faceWarningActive && audioWarningActive) {
      message = (audioWarningSince >= faceWarningSince) ? audioWarningMsg : faceWarningMsg;
    } else if (faceWarningActive) {
      message = faceWarningMsg;
    } else if (audioWarningActive) {
      message = audioWarningMsg;
    }

    if (active) {
      preview.classList.add('warn');
      statusPill.classList.add('warn');
      statusPill.textContent = 'Warning';
      warningBanner.textContent = message || 'Please stay attentive.';
      warningBanner.style.display = 'block';
    } else {
      preview.classList.remove('warn');
      statusPill.classList.remove('warn');
      statusPill.textContent = 'Monitoring Active';
      warningBanner.style.display = 'none';
    }
  }

  const FACE_WARNING_TYPES = [
    'phone_warning','head_direction_warning','head_pitch_warning',
    'head_roll_warning','eyes_closed_warning','gaze_warning',
    'mouth_warning','multiple_face_warning','no_face_warning','face_warning','lighting_warning'
  ];

  function legacyTypeFromMessage(msg){
    if (/too dark|dim/i.test(msg)) return 'lighting_warning';
    if (/phone/i.test(msg)) return 'phone_warning';
    if (/Multiple faces|Other person/i.test(msg)) return 'multiple_face_warning';
    if (/Face not detected/i.test(msg)) return 'no_face_warning';
    if (/Eyes closed/i.test(msg)) return 'eyes_closed_warning';
    if (/Eyes are not looking/i.test(msg)) return 'gaze_warning';
    if (/Mouth movement/i.test(msg)) return 'mouth_warning';
    if (/look straight/i.test(msg)) return 'head_direction_warning';
    if (/face straight/i.test(msg)) return 'head_pitch_warning';
    if (/head straight|tilt/i.test(msg)) return 'head_roll_warning';
    return 'face_warning';
  }

  function updateStats(stats){
    stats = stats || {};
    monitorOkAt = Date.now();
    if (stats.terminate && window.__aiTerminate) {
      window.__aiTerminate(stats.terminate_reason || 'no_face_timeout');
    }
    const wasActive = faceWarningActive;
    faceWarningActive = !!stats.warning;
    faceWarningMsg = stats.warning_message || '';
    if (faceWarningActive && !wasActive) faceWarningSince = Date.now();
    refreshWarningUI();

    // The server may report several simultaneous problems (e.g. phone AND
    // another person). Each distinct type counts once per occurrence.
    let list = Array.isArray(stats.warnings) ? stats.warnings.slice() : [];
    if (!list.length && stats.warning) {
      const m = stats.warning_message || 'Attention warning detected';
      list = [{type: stats.warning_type || legacyTypeFromMessage(m), message: m}];
    }
    const activeTypes = new Set();
    list.forEach(w => {
      if (!w || !w.type) return;
      activeTypes.add(w.type);
      if (window.__aiRegisterWarning) window.__aiRegisterWarning(w.type, w.message || 'Warning');
    });
    if (window.__aiClearWarningType) {
      FACE_WARNING_TYPES.forEach(t => { if (!activeTypes.has(t)) window.__aiClearWarningType(t); });
    }
    if (list.length > 1) {
      faceWarningMsg = list.map(w => w.message).join(' | ');
      refreshWarningUI();
    }
  }

  function updateAudioStatus(data){
    const wasActive = audioWarningActive;
    audioWarningActive = !!data.warning;
    audioWarningMsg = data.warning_message || '';
    if (audioWarningActive && !wasActive) audioWarningSince = Date.now();
    refreshWarningUI();

    if (data.warning && window.__aiRegisterWarning) {
      window.__aiRegisterWarning('audio_warning', data.warning_message || 'Audio detected');
    } else if (!data.warning && window.__aiClearWarningType) {
      window.__aiClearWarningType('audio_warning');
    }
  }

  // ===================== AUDIO LEVEL MONITORING =====================
  // Local detector: it only raises an event after sustained loud input. This
  // avoids the old 500 ms request queue that could deliver a stale warning long
  // after the student had already stopped speaking.
  function startAudioMonitoring(mediaStream){
    try {
      const tracks = mediaStream.getAudioTracks();
      if (!tracks.length) return;
      const audioContext = new (window.AudioContext || window.webkitAudioContext)();
      const analyser = audioContext.createAnalyser();
      const source = audioContext.createMediaStreamSource(mediaStream);
      source.connect(analyser);
      analyser.fftSize = 2048;
      const dataArray = new Uint8Array(analyser.fftSize);

      const tryResume = () => {
        if (audioContext.state === 'suspended') audioContext.resume().catch(()=>{});
      };
      tryResume();
      ['click','keydown','pointerdown','pointermove','touchstart','focus'].forEach(ev => document.addEventListener(ev, tryResume, {passive:true}));
      window.__aiResumeAudioContext = tryResume;

      let calibration = [];
      let baseline = 0.006;
      let lastWarningAt = 0;
      const recent = [];           // last 5 readings: true = loud
      const calibrationEnd = Date.now() + 4000;
      const ABSOLUTE = 0.011;      // lowest level ever treated as speech
      const COOLDOWN = 8000;       // quiet time needed before the next strike
      let silentTicks = 0, micAlertAt = 0, micMutedWarned = false;

      const freq = new Uint8Array(analyser.frequencyBinCount);
      const binHz = audioContext.sampleRate / analyser.fftSize;
      const lo = Math.floor(250 / binHz), hi = Math.ceil(3400 / binHz);

      const timer = setInterval(() => {
        if (submitting) return;
        tryResume();
        if (audioContext.state !== 'running') return;

        analyser.getByteTimeDomainData(dataArray);
        let sum = 0;
        for (let i=0; i<dataArray.length; i++) {
          const n = (dataArray[i] - 128) / 128;
          sum += n*n;
        }
        const level = Math.sqrt(sum / dataArray.length);

        // How much of the sound sits in the human-voice band (250-3400 Hz).
        analyser.getByteFrequencyData(freq);
        // (Average strength inside the voice band compared with the average over
        // all frequencies. The old version compared the SUM, but the voice band is
        // only ~13% of all frequency slots, so real speech could never pass.)
        let band = 0, all = 0;
        for (let i=1; i<freq.length; i++) { all += freq[i]; if (i>=lo && i<=hi) band += freq[i]; }
        const bandMean = band / Math.max(1, hi - lo + 1);
        const allMean = all / Math.max(1, freq.length - 1);
        const voiceShare = allMean > 0 ? bandMean / allMean : 0;

        // ---- microphone health: a dead / muted mic must be noticed, not ignored
        const tr = mediaStream.getAudioTracks()[0];
        const dead = !tr || tr.readyState === 'ended' || tr.muted || level < 0.0006;
        silentTicks = dead ? silentTicks + 1 : 0;
        if (silentTicks >= 80 && !micMutedWarned) {      // 20 s of complete silence: muted / unplugged
          micMutedWarned = true;
          try { if (window.__aiRegisterWarning) window.__aiRegisterWarning('mic_muted', 'Microphone is muted or not working. Keep it on during the exam.'); } catch(e) {}
        }
        if (silentTicks >= 60 && Date.now() - micAlertAt > 60000) {   // 15 s of nothing
          micAlertAt = Date.now();
          try { status('\u26A0 Microphone is not picking up any sound'); } catch(e) {}
          try { fetch('/student/exam/violation', {method:'POST', credentials:'same-origin', keepalive:true,
            headers:{'Content-Type':'application/json'},
            body: JSON.stringify({type:'mic_silent', message:'Microphone is silent / muted during the exam', exam_id: examId, timestamp: new Date().toISOString()})}).catch(()=>{}); } catch(e) {}
        }

        if (Date.now() < calibrationEnd) {
          calibration.push(level);
          calibration = calibration.slice(-20);
          if (calibration.length >= 5) {
            const sorted = calibration.slice().sort((a,b)=>a-b);
            baseline = sorted[Math.floor(sorted.length * 0.25)] || baseline;   // quiet part only
          }
          return;
        }

        // Track only the quiet baseline; never let loud audio raise the baseline.
        if (level < Math.max(0.03, baseline * 1.25)) {
          baseline = baseline * 0.98 + level * 0.02;
        }

        const threshold = Math.max(ABSOLUTE, baseline * 2.0 + 0.006);
        const loud = level >= threshold && voiceShare > 0.85;
        recent.push(loud); if (recent.length > 5) recent.shift();
        const loudCount = recent.filter(Boolean).length;

        // Speaking = at least 3 loud readings out of the last 5 (about 1 second).
        // A genuinely quiet spell (4 of the last 5 quiet) closes the event, so a
        // new speaking episode counts again but one long chat is not 3 strikes.
        if (loudCount <= 1 && audioWarningActive && Date.now() - lastWarningAt > COOLDOWN) {
          updateAudioStatus({warning:false, warning_message:''});
        }

        if (loudCount >= 3 && !audioWarningActive) {
          recent.length = 0;
          lastWarningAt = Date.now();
          updateAudioStatus({
            warning: true,
            warning_message: '\uD83D\uDD0A Voice / sound detected. Please stay silent during the examination.',
            audio_level: level,
            baseline: baseline
          });
          fetch('/student/exam/audio-warning', {
            method: 'POST',
            credentials: 'same-origin',
            keepalive: true,
            headers: {'Content-Type':'application/json'},
            body: JSON.stringify({exam_id: examId, audio_level: level, baseline: baseline})
          }).catch(()=>{});
        }
      }, 250);

      window.__aiStopAudioMonitoring = () => {
        clearInterval(timer);
        ['click','keydown','pointerdown','pointermove','touchstart','focus'].forEach(ev => document.removeEventListener(ev, tryResume));
        try { audioContext.close(); } catch(e) {}
      };
    } catch (e) {
      console.error('Audio monitoring setup error:', e);
    }
  }

  // ===================== LIVE AUDIO FOR ADMIN MONITORING =====================
  // Records short (~2.2s) audio-only clips on a loop and uploads each
  // one as it finishes, overwriting the previous clip on the server.
  // The separate admin app polls and plays the latest clip — this
  // gives admin near-live sound (a couple seconds of lag, not a
  // perfect real-time call) without needing WebRTC/WebSocket
  // infrastructure, using the same simple upload-and-poll pattern
  // already used for the live video frames.
  function startLiveAudioChunkLoop(mediaStream){
    const audioTracks = mediaStream.getAudioTracks();
    if (!audioTracks.length) return;

    const audioOnlyStream = new MediaStream(audioTracks);

    function recordChunk(){
      if (submitting) return;

      let chunkParts = [];
      let chunkRecorder;

      try {
        const types = ['audio/webm;codecs=opus', 'audio/webm'];
        const mime = types.find(t => MediaRecorder.isTypeSupported(t)) || '';
        chunkRecorder = new MediaRecorder(audioOnlyStream, mime ? {mimeType: mime} : undefined);
      } catch (e) {
        console.error('Live audio chunk recorder error:', e);
        return;
      }

      chunkRecorder.ondataavailable = e => {
        if (e.data && e.data.size) chunkParts.push(e.data);
      };

      chunkRecorder.onstop = () => {
        if (chunkParts.length) {
          const blob = new Blob(chunkParts, {type: chunkRecorder.mimeType || 'audio/webm'});
          const fd = new FormData();
          fd.append('audio', blob, 'chunk.webm');
          fetch('/student/exam/live-audio-chunk', {method: 'POST', body: fd}).catch(() => {});
        }
        if (!submitting) setTimeout(recordChunk, 150);
      };

      chunkRecorder.start();
      setTimeout(() => {
        if (chunkRecorder.state !== 'inactive') chunkRecorder.stop();
      }, 2200);
    }

    recordChunk();
  }

  // ===================== FAST LIVE CAMERA FRAME TO ADMIN =====================
  // The admin monitoring grid uses the latest JPEG frame, not WebRTC.
  // WebRTC is intentionally NOT used for the grid because repeatedly
  // creating/retrying peer connections was producing CONNECTING tiles and
  // unnecessary latency. AI analysis remains on its own 1.5s loop.
  let liveFrameTimer = null;
  let liveFrameInFlight = false;

  async function sendLatestLiveFrame(){
    if (submitting || !video.videoWidth || liveFrameInFlight) return;
    liveFrameInFlight = true;
    try {
      // Reuse the existing hidden canvas. This is only a JPEG snapshot;
      // it does NOT run MediaPipe and therefore stays fast.
      ctx.drawImage(video, 0, 0, canvas.width, canvas.height);
      const imageData = canvas.toDataURL('image/jpeg', 0.55);
      await fetchWithTimeout('/student/exam/live-frame', {
        method: 'POST',
        headers: {'Content-Type': 'application/json'},
        credentials: 'same-origin',
        body: JSON.stringify({image: imageData, exam_id: examId})
      }, 7000);
    } catch (e) {
      console.debug('[LIVE FRAME] upload', e);
    } finally {
      liveFrameInFlight = false;
    }
  }

  function startLiveFrameLoop(){
    sendLatestLiveFrame();
    liveFrameTimer = setInterval(sendLatestLiveFrame, 900);
  }

  // ===================== DIRECT CAMERA WEBRTC TO ADMIN =====================
  // The <video> element above is already receiving the student's real camera
  // MediaStream. We publish that SAME stream to the admin through WebRTC.
  // This is the direct path used by Live Monitoring; JPEG syncing remains only
  // as a fallback/status mechanism.
  let adminVideoSignalTimer = null;
  let adminVideoPc = null;
  let lastVideoOfferFingerprint = '';
  let videoAnswerInFlight = false;

  async function waitForIceGathering(pc, timeoutMs=5000){
    if(pc.iceGatheringState === 'complete') return;
    await new Promise(resolve=>{
      let done=false;
      const finish=()=>{
        if(done) return; done=true;
        clearTimeout(timer);
        pc.removeEventListener('icegatheringstatechange', check);
        resolve();
      };
      const check=()=>{ if(pc.iceGatheringState==='complete') finish(); };
      const timer=setTimeout(finish, timeoutMs);
      pc.addEventListener('icegatheringstatechange', check);
      check();
    });
  }

  async function handleAdminVideoOffer(offer){
    if(!offer || !stream || submitting || videoAnswerInFlight) return;
    const fingerprint = JSON.stringify(offer);
    if(fingerprint === lastVideoOfferFingerprint && adminVideoPc) return;
    videoAnswerInFlight=true;
    try{
      if(adminVideoPc){ try{adminVideoPc.close();}catch(e){} adminVideoPc=null; }
      const pc=new RTCPeerConnection({iceServers:ICE_SERVERS});
      adminVideoPc=pc;
      // Publish the EXACT MediaStream already shown in the student's preview.
      // IMPORTANT: this is one WebRTC connection carrying BOTH tracks.
      const videoTrack = stream.getVideoTracks()[0];
      const audioTrack = stream.getAudioTracks()[0];
      if(!videoTrack) throw new Error('Camera video track is missing');
      if(!audioTrack) throw new Error('Microphone audio track is missing');
      pc.addTrack(videoTrack, stream);
      pc.addTrack(audioTrack, stream);
      console.log('[LIVE WEBRTC] publishing camera + microphone');
      await pc.setRemoteDescription(new RTCSessionDescription(offer));
      const answer=await pc.createAnswer();
      await pc.setLocalDescription(answer);
      await waitForIceGathering(pc);
      const res=await fetch('/student/exam/video/answer',{
        method:'POST',
        headers:{'Content-Type':'application/json'},
        credentials:'same-origin',
        body:JSON.stringify({exam_id:examId,answer:pc.localDescription})
      });
      if(!res.ok) throw new Error('video answer HTTP '+res.status);
      lastVideoOfferFingerprint=fingerprint;
      pc.onconnectionstatechange=()=>{
        if(['failed','closed'].includes(pc.connectionState) && adminVideoPc===pc){
          adminVideoPc=null;
          lastVideoOfferFingerprint='';
        }
      };
    }catch(e){
      console.debug('[LIVE VIDEO] answer',e);
      if(adminVideoPc){try{adminVideoPc.close();}catch(_){} adminVideoPc=null;}
      lastVideoOfferFingerprint='';
    }finally{ videoAnswerInFlight=false; }
  }

  async function pollAdminVideoOffer(){
    if(submitting || !stream) return;
    try{
      const res=await fetch('/student/exam/video/poll?exam_id='+encodeURIComponent(examId),{cache:'no-store',credentials:'same-origin'});
      if(!res.ok) return;
      const data=await res.json();
      if(data.success && data.offer) await handleAdminVideoOffer(data.offer);
    }catch(e){ /* admin may not be viewing Live Monitoring yet */ }
  }

  function startAdminVideoSignal(){
    pollAdminVideoOffer();
    adminVideoSignalTimer=setInterval(pollAdminVideoOffer,700);
  }

  let livePresenceTimer = null;
  async function sendLivePresence(){
    if (submitting) return;
    try {
      await fetch('/student/exam/live-presence',{
        method:'POST', headers:{'Content-Type':'application/json'}, credentials:'same-origin',
        body:JSON.stringify({exam_id:examId})
      });
    } catch(e) {}
  }
  function startLivePresence(){
    sendLivePresence();
    livePresenceTimer=setInterval(sendLivePresence,1500);
  }

  window.__aiStopLiveVideo=()=>{
    // Kept under the old public name so the existing submit/timeout cleanup
    // code continues to work. It now stops the JPEG live-frame loop.
    if(liveFrameTimer) clearInterval(liveFrameTimer);
    liveFrameTimer=null;
    liveFrameInFlight=false;
    if(livePresenceTimer) clearInterval(livePresenceTimer);
    livePresenceTimer=null;
    if(adminVideoSignalTimer) clearInterval(adminVideoSignalTimer);
    adminVideoSignalTimer=null;
    if(adminVideoPc){try{adminVideoPc.close();}catch(e){} adminVideoPc=null;}
    lastVideoOfferFingerprint='';
  };

  async function start(){
    const form = getExamForm();
    if (!form) return;
    addHiddenField(form);
    addHiddenField(form, 'recording_token');

    try {
      stream = await navigator.mediaDevices.getUserMedia({
        video: {width:{ideal:640}, height:{ideal:480}, frameRate:{ideal:15, max:24}, facingMode:'user'},
        audio: {
          echoCancellation: true, noiseSuppression: false, autoGainControl: true,
          ...(window.__aiAudioDeviceId ? {deviceId: {exact: window.__aiAudioDeviceId}} : {})
        }
      });
      if (!stream.getAudioTracks().length) { throw new Error('No microphone track'); }
      stream.getAudioTracks().forEach(t => { t.enabled = true; });
      video.srcObject = stream;
      primeAdminVoiceAudio();

      const types = ['video/webm;codecs=vp9,opus','video/webm;codecs=vp8,opus','video/webm'];
      const mime = types.find(t => MediaRecorder.isTypeSupported(t)) || '';
      recordingToken = makeRecordingToken();
      // Keep the whole file under Cloudinary's 100 MB (free plan) video limit and
      // quick to hand over: budget about 90 MB of video + sound for the exam length,
      // so a 2 or 3 hour exam gives a grainier but still usable picture.
      const AUDIO_BPS = 24000;
      const totalBits = Math.floor(90e6 * 8 / Math.max(300, EXAM_DURATION_MIN * 60 + 180));
      const targetBits = Math.max(30000, Math.min(380000, totalBits - AUDIO_BPS));
      const recOpts = mime ? {mimeType:mime} : {};
      recOpts.videoBitsPerSecond = targetBits; recOpts.audioBitsPerSecond = AUDIO_BPS;
      try { recorder = new MediaRecorder(stream, recOpts); } catch (e) { recorder = new MediaRecorder(stream, mime ? {mimeType:mime} : undefined); }
      recorder.ondataavailable = e => {
        if (e.data && e.data.size) queueRecordingPart(e.data);
      };
      recorder.start(2000);
      status('\u25CF Recording');

      startMonitoringLoop();
      startAudioMonitoring(stream);
      startLiveAudioChunkLoop(stream);
      startLivePresence();
      startLiveFrameLoop();
      // Start the admin camera signaling ONLY after the real camera stream
      // exists. Without this call the student never polls for the admin
      // WebRTC offer, so the admin card remains stuck on "CONNECTING CAMERA".
      startAdminVideoSignal();
    } catch (e) {
      console.error(e);
      status('Camera unavailable');
      alert('Camera and microphone access are required for exam monitoring. Please allow access and reload the page.');
      return;
    }

    HTMLFormElement.prototype.submit = function(){
      if (this === form) { stopAndSubmit(this); return; }
      nativeSubmit.call(this);
    };

    form.addEventListener('submit', e => {
      if (submitting) return;
      e.preventDefault();
      stopAndSubmit(form);
    }, true);


    // Timeout uses the same reliable recording/save flow as warning and fullscreen termination.
    window.__aiSubmitExamAtTimeout = () => {
      if (submitting) return;
      let reasonInput = form.querySelector('input[name="termination_reason"]');
      if (!reasonInput) { reasonInput=document.createElement('input'); reasonInput.type='hidden'; reasonInput.name='termination_reason'; form.appendChild(reasonInput); }
      reasonInput.value='time_expired';
      stopAndSubmit(form);
    };
    window.__aiStopExamSubmit = () => stopAndSubmit(form);
  }

  // Exposed so the "Start Exam" button (in the fullscreen-lockdown
  // script) can trigger this from inside its own click handler.
  // Starting camera/mic/audio-analysis from a genuine click, instead
  // of automatically on page load, is required for the browser to
  // treat the AudioContext as user-activated — without this, mic
  // level analysis can silently read near-zero forever, no matter
  // how loud the student is.
  window.__aiStartMonitoring = start;

  // ===================== ADMIN VOICE BROADCAST =====================
  // Receives one-way audio from the admin through WebRTC. The student
  // never publishes a microphone track to the admin for this feature.
  let adminVoicePC = null;
  let adminVoiceOffer = null;
  let adminVoiceTimer = null;
  window.__aiExamStarted = false;
  const adminVoiceAudio = document.createElement('audio');
  adminVoiceAudio.autoplay = true;
  adminVoiceAudio.setAttribute('playsinline', '');
  adminVoiceAudio.volume = 1;
  adminVoiceAudio.style.display = 'none';
  document.body.appendChild(adminVoiceAudio);

  // Prime the audio element from the student's real exam-start gesture.
  // This helps browsers that apply strict autoplay policies.
  function primeAdminVoiceAudio(){
    adminVoiceAudio.play().catch(() => {});
  }

  async function waitForVoiceIceComplete(pc){
    if (pc.iceGatheringState === 'complete') return;
    await new Promise(resolve => {
      const timeout = setTimeout(resolve, 8000);
      const check = () => {
        if (pc.iceGatheringState === 'complete') {
          clearTimeout(timeout);
          pc.removeEventListener('icegatheringstatechange', check);
          resolve();
        }
      };
      pc.addEventListener('icegatheringstatechange', check);
    });
  }

  function closeAdminVoice(){
    if (adminVoicePC) { try { adminVoicePC.close(); } catch(e){} }
    adminVoicePC = null;
    adminVoiceOffer = null;
    adminVoiceAudio.srcObject = null;
  }

  async function pollAdminVoice(){
    if (submitting || !window.__aiExamStarted) return;
    try {
      const r = await fetch(`/student/exam/voice/poll?exam_id=${encodeURIComponent(examId)}`, {cache:'no-store'});
      const data = await r.json();
      if (!data.success || !data.offer) {
        if (!data.success) closeAdminVoice();
        return;
      }

      const offerKey = JSON.stringify(data.offer);
      if (offerKey === adminVoiceOffer && adminVoicePC && adminVoicePC.connectionState !== 'closed') return;

      closeAdminVoice();
      adminVoiceOffer = offerKey;
      adminVoicePC = new RTCPeerConnection({ iceServers: ICE_SERVERS });

      adminVoicePC.ontrack = event => {
        const stream = event.streams && event.streams[0];
        if (stream) {
          adminVoiceAudio.srcObject = stream;
          adminVoiceAudio.play().catch(() => {});
        }
      };
      adminVoicePC.onconnectionstatechange = () => {
        if (['failed','closed'].includes(adminVoicePC.connectionState)) closeAdminVoice();
      };

      await adminVoicePC.setRemoteDescription(new RTCSessionDescription(data.offer));
      const answer = await adminVoicePC.createAnswer();
      await adminVoicePC.setLocalDescription(answer);
      await waitForVoiceIceComplete(adminVoicePC);

      await fetch('/student/exam/voice/answer', {
        method:'POST', headers:{'Content-Type':'application/json'},
        body:JSON.stringify({exam_id:examId, answer:adminVoicePC.localDescription})
      });
    } catch(e) {
      console.debug('[VOICE] student poll', e);
    }
  }

  adminVoiceTimer = setInterval(pollAdminVoice, 1000);
  pollAdminVoice();

  window.__aiStopAdminVoice = () => {
    if (adminVoiceTimer) clearInterval(adminVoiceTimer);
    adminVoiceTimer = null;
    closeAdminVoice();
  };

  status('Waiting for exam to start...');
})();
</script>
"""



FULLSCREEN_AUTOEND_SCRIPT = r"""
<style>
#ai-fs-start-overlay{
    position:fixed;inset:0;background:#0b0f18;z-index:2147483600;
    display:flex;align-items:center;justify-content:center;text-align:center;
    font-family:'Segoe UI',Arial,sans-serif;color:#e8eaf0;
}
#ai-fs-start-overlay .box{max-width:480px;padding:24px;max-height:96vh;overflow:auto}
#ai-sc{background:#111827;border:1px solid #27324d;border-radius:12px;padding:14px 16px;margin:0 0 16px;text-align:left}
#ai-sc .sc-title{font-weight:700;font-size:14px;margin-bottom:10px;color:#e8eaf0}
#ai-sc .sc-row{display:flex;gap:10px;align-items:flex-start;padding:8px 0;border-top:1px solid #1e2740}
#ai-sc .sc-row:first-of-type{border-top:0}
#ai-sc .sc-ic{flex:0 0 24px;height:24px;border-radius:50%;display:grid;place-items:center;font-size:13px;font-weight:800;background:#1e2740;color:#8891a8}
#ai-sc .sc-row.ok .sc-ic{background:#16a34a;color:#fff}
#ai-sc .sc-row.bad .sc-ic{background:#dc2626;color:#fff}
#ai-sc .sc-row.run .sc-ic{background:#2563eb;color:#fff;animation:ai-sc-pulse 1s infinite}
@keyframes ai-sc-pulse{50%{opacity:.45}}
#ai-sc b{display:block;font-size:13.5px;color:#e8eaf0}
#ai-sc small{display:block;font-size:12.5px;color:#9aa4bd;line-height:1.5;margin-top:2px}
#ai-sc .sc-meter{height:6px;border-radius:99px;background:#1e2740;overflow:hidden;margin:8px 0 2px}
#ai-sc .sc-meter i{display:block;height:100%;width:0;background:linear-gradient(90deg,#22c55e,#facc15,#ef4444);transition:width .08s linear}
#ai-sc select{width:100%;margin-top:8px;background:#0b1220;color:#e8eaf0;border:1px solid #27324d;border-radius:8px;padding:7px;font-size:12.5px}
#ai-sc-btn{margin-top:10px;width:100%;background:#2563eb;color:#fff;border:0;border-radius:8px;padding:10px;font-weight:700;font-size:14px;cursor:pointer}
#ai-sc-btn:disabled{opacity:.6;cursor:default}
#ai-fs-start-btn:disabled{background:#334155;color:#94a3b8;cursor:not-allowed}
#ai-sc-pop{font-family:'Segoe UI',Arial,sans-serif;position:fixed;inset:0;background:rgba(2,6,18,.78);z-index:2147483640;display:none;align-items:center;justify-content:center}
#ai-sc-pop.show{display:flex}
#ai-sc-pop .pbox{width:min(420px,92vw);background:#121a2e;border:1px solid #f59e0b;border-radius:14px;padding:24px;text-align:center;box-shadow:0 20px 60px rgba(0,0,0,.6)}
#ai-sc-pop h2{margin:0 0 10px;font-size:19px;color:#fbbf24}
#ai-sc-pop p{margin:0 0 16px;font-size:14px;line-height:1.6;color:#d3d9ea}
#ai-sc-pop button{background:#6366f1;color:#fff;border:0;border-radius:8px;padding:9px 28px;font-weight:700;cursor:pointer}
#ai-fs-start-overlay .eyebrow{font:600 11.5px monospace;letter-spacing:.08em;
    text-transform:uppercase;color:#5b8cff;margin-bottom:12px}
#ai-fs-start-overlay h1{font-size:22px;margin:0 0 12px}
#ai-fs-start-overlay p{color:#8891a8;font-size:14px;margin-bottom:18px;line-height:1.6}
#ai-fs-start-overlay ul{text-align:left;color:#8891a8;font-size:13px;
    margin-bottom:10px;padding-left:20px;line-height:1.8}
#ai-fs-start-overlay .danger-note{background:#2c1616;border:1px solid #5c2a2a;
    color:#fecaca;border-radius:8px;padding:12px 14px;font-size:13px;margin-bottom:22px;text-align:left}
#ai-fs-start-btn{background:#5b8cff;color:#fff;border:none;padding:13px 26px;
    border-radius:8px;font-size:15px;font-weight:600;cursor:pointer;width:100%}
#ai-fs-start-btn:hover{background:#4a76e6}

#ai-fs-ending-overlay{
    position:fixed;inset:0;background:rgba(11,15,24,.98);z-index:2147483650;
    display:none;align-items:center;justify-content:center;text-align:center;
    font-family:'Segoe UI',Arial,sans-serif;color:#e8eaf0;
}
#ai-fs-ending-overlay .box{max-width:420px;padding:24px}
#ai-fs-ending-overlay h1{color:#f87171;font-size:20px;margin:0 0 12px}
#ai-fs-ending-overlay p{color:#8891a8;font-size:14px}
#ai-fs-spinner{width:34px;height:34px;border:3px solid #262e44;border-top-color:#f87171;
    border-radius:50%;margin:0 auto 18px;animation:ai-spin 0.8s linear infinite}
@keyframes ai-spin{to{transform:rotate(360deg)}}

#ai-violation-toast{
    position:fixed;top:16px;left:50%;transform:translateX(-50%);
    background:#2c1616;border:1px solid #f87171;color:#fecaca;
    padding:10px 20px;border-radius:8px;font:13.5px 'Segoe UI',Arial,sans-serif;
    z-index:2147483601;display:none;text-align:center;max-width:80vw;
}
#ai-warning-count{
    position:fixed;top:16px;right:18px;z-index:2147483400;
    background:#141a29;border:1px solid #262e44;color:#e8eaf0;
    padding:6px 14px;border-radius:20px;font:600 12.5px 'Segoe UI',Arial,sans-serif;
}
#ai-warning-count.active{background:#2c1616;border-color:#5c2a2a;color:#f87171}
#ai-keyboard-status{position:fixed;top:54px;right:18px;z-index:2147483400;background:#141a29;border:1px solid #262e44;color:#e8eaf0;padding:6px 14px;border-radius:20px;font:600 12.5px 'Segoe UI',Arial,sans-serif}
#ai-keyboard-status.unlocked{background:#12351f;border-color:#2f7a49;color:#86efac}
#ai-result-lock-overlay{position:fixed;inset:0;z-index:2147483646;pointer-events:none;display:flex;align-items:flex-start;justify-content:center;padding-top:70px;background:rgba(5,8,16,.20);font-family:'Segoe UI',Arial,sans-serif}
#ai-result-lock-overlay .ai-result-lock-box{pointer-events:none;max-width:440px;margin:0 18px;padding:18px 22px;text-align:center;border:1px solid rgba(248,113,113,.55);border-radius:12px;background:rgba(12,16,28,.94);box-shadow:0 12px 40px rgba(0,0,0,.45);color:#f1f0f7}
#ai-result-lock-overlay h2{margin:0 0 8px;color:#86efac;font-size:20px}
#ai-result-lock-overlay p{margin:5px 0;color:#d7dbea;font-size:13px;line-height:1.5}
#ai-result-lock-overlay .ai-result-lock-icon{font-size:24px;margin-bottom:5px}
#ai-result-lock-overlay .ai-result-lock-small{color:#aeb6ca;font-size:12px}
</style>

<div id="ai-warning-count">Warnings: 0 / 3</div>
<div id="ai-keyboard-status">Keyboard: Locked</div>

<div id="ai-fs-start-overlay">
  <div class="box">
    <div class="eyebrow">Before You Begin</div>
    <h1>Exam Monitoring Notice</h1>
    <p>This exam runs in fullscreen mode with live webcam, microphone, and activity monitoring.</p>
    <ul>
      <li>The exam will enter fullscreen mode on start</li>
      <li>Your session is recorded for review by your instructor</li>
      <li>Your admin can view your live camera feed on a separate monitoring system</li>
      <li><strong>Your keyboard is completely locked once the exam starts</strong> — use the mouse only. After the exam, unlock it with the on-screen keyboard.</li>
    </ul>
    <div class="danger-note">
      &#9888; If you exit fullscreen or switch tabs/windows at any point, your exam will be
      <strong>automatically submitted immediately</strong> with your answers as they are at that moment.
    </div>
    <div id="ai-sc" style="display:none">
      <div class="sc-title">Sound &amp; microphone check (required)</div>
      <div class="sc-row" id="sc-vol"><span class="sc-ic">1</span><div><b>Computer volume at 100%</b><small id="sc-vol-t">Set your computer volume to 100%, then press the button below. A short beep will play and your microphone must hear it.</small></div></div>
      <div class="sc-row" id="sc-mic"><span class="sc-ic">2</span><div><b>Microphone works</b><small id="sc-mic-t">After the volume check, say &ldquo;I am ready&rdquo; aloud.</small><div class="sc-meter"><i id="sc-meter-i"></i></div></div></div>
      <select id="sc-dev" style="display:none" title="Microphone"></select>
      <button type="button" id="ai-sc-btn">Start sound check</button>
    </div>
    <button id="ai-fs-start-btn" disabled>Enter Fullscreen &amp; Start Exam</button>
  </div>
</div>
<div id="ai-sc-pop"><div class="pbox"><h2 id="ai-sc-pop-t"></h2><p id="ai-sc-pop-m"></p><button type="button" id="ai-sc-pop-ok">OK</button></div></div>

<div id="ai-fs-ending-overlay">
  <div class="box">
    <div id="ai-fs-spinner"></div>
    <h1 id="ai-fs-ending-title">Exam Ending</h1>
    <p id="ai-fs-ending-msg">A violation was detected. Submitting your exam automatically...</p>
  </div>
</div>

<div id="ai-violation-toast"></div>

<script>
(() => {
  const examId = decodeURIComponent(location.pathname.split('/').filter(Boolean).pop());
  const startOverlay = document.getElementById('ai-fs-start-overlay');
  const endingOverlay = document.getElementById('ai-fs-ending-overlay');
  const endingMsg = document.getElementById('ai-fs-ending-msg');
  const startBtn = document.getElementById('ai-fs-start-btn');
  const toast = document.getElementById('ai-violation-toast');

  let examStarted = false;
  let examEnding = false;
  // FIX: entering fullscreen (and the camera/mic permission prompt
  // right before it) can itself cause a brief, spurious
  // visibilitychange/blur blip on some browsers/OSes — the page
  // isn't actually hidden or unfocused, it's just settling into the
  // fullscreen transition. Treating that instant as "student
  // switched tabs" was ending the exam within moments of the
  // student clicking Start, before they ever saw a question. A
  // short grace window right after start, plus a re-check before
  // acting on visibility loss, filters that out while still catching
  // a real, sustained tab switch later in the exam.
  let examStartGraceUntil = 0;
  let resultLocked = false;
  let tabViolationCount = 0;
  let keyboardUnlocked = false;
  let unlockBuffer = '';
  let unlockCheckTimer = null;

  // =====================================================
  // SHARED WARNING COUNTER (3 strikes -> auto-submit)
  // Covers: face/eye/head AI warnings, audio detection,
  // window losing focus, blocked keyboard shortcuts.
  // Fullscreen-exit and tab-switch remain separate INSTANT
  // auto-end triggers (handled below), not part of this count.
  // =====================================================
  const MAX_WARNINGS = 3;

  // A warning is an EVENT, not every AI poll while the same condition
  // remains true. The old 1-second cooldown was shorter than the 1.5s
  // AI polling interval, so one persistent condition (for example a
  // slightly wrong head angle) became warning #1, #2 and #3 within
  // about 4.5 seconds. That made a normal student look like malpractice.
  //
  // Each warning type is therefore latched until that condition clears.
  // It can count again only after the detector reports that type as clear.
  const warningActiveTypes = new Set();
  let totalWarnings = 0;
  const warningCountEl = document.getElementById('ai-warning-count');

  window.__aiRegisterWarning = function(type, message){
    if (!examStarted || examEnding) return;

    // Ignore the camera/fullscreen settling period immediately after start.
    if (Date.now() < examStartGraceUntil) return;

    type = String(type || 'face_warning');
    if (warningActiveTypes.has(type)) return; // same ongoing event

    warningActiveTypes.add(type);
    totalWarnings++;

    if (warningCountEl) {
      warningCountEl.textContent = `Warnings: ${totalWarnings} / ${MAX_WARNINGS}`;
      warningCountEl.classList.add('active');
    }

    logViolation(type, `${message} (warning ${totalWarnings}/${MAX_WARNINGS})`);
    showToast(`\u26A0 Warning ${totalWarnings}/${MAX_WARNINGS}: ${message}`);

    if (totalWarnings >= MAX_WARNINGS) {
      autoEndExam(
        `You reached the maximum of ${MAX_WARNINGS} warnings.`,
        'max_warnings_reached',
        `Student reached ${MAX_WARNINGS} warnings \u2014 exam auto-submitted`
      );
    }
  };

  window.__aiClearWarningType = function(type){
    warningActiveTypes.delete(String(type || 'face_warning'));
  };

  // The camera has shown nobody for too long: end the exam straight away.
  window.__aiTerminate = function(reason){
    if (!examStarted || examEnding) return;
    if (Date.now() < examStartGraceUntil) return;
    autoEndExam(
      'Your face was not visible for too long.',
      String(reason || 'no_face_timeout'),
      'Face not visible for too long \u2014 exam auto-submitted'
    );
  };

  function showToast(msg){
    toast.textContent = msg;
    toast.style.display = 'block';
    clearTimeout(showToast._t);
    showToast._t = setTimeout(() => { toast.style.display = 'none'; }, 3000);
  }

  function enterFullscreen(){
    const el = document.documentElement;
    if (el.requestFullscreen) return el.requestFullscreen();
    if (el.webkitRequestFullscreen) return el.webkitRequestFullscreen();
    if (el.msRequestFullscreen) return el.msRequestFullscreen();
    return Promise.resolve();
  }

  function isFullscreen(){
    return !!(document.fullscreenElement || document.webkitFullscreenElement || document.msFullscreenElement);
  }

  window.__aiExitFullscreen = () => {
    if (isFullscreen() && document.exitFullscreen) document.exitFullscreen().catch(()=>{});
  };

  function logViolation(type, message){
    fetch('/student/exam/violation', {
      method: 'POST',
      keepalive: true,
      headers: {'Content-Type':'application/json'},
      body: JSON.stringify({type, message, exam_id: examId, timestamp: new Date().toISOString()})
    }).catch(()=>{});
  }

  function logTabViolation(message){
    tabViolationCount++;
    fetch('/tab_violation', {
      method: 'POST',
      keepalive: true,
      headers: {'Content-Type':'application/json'},
      body: JSON.stringify({violation_count: tabViolationCount, message, exam_id: examId})
    }).catch(()=>{});
  }

  function autoEndExam(reasonLabel, violationType, violationMessage){
    if (examEnding || !examStarted) return;
    examEnding = true;
    examStarted = false;
    window.__aiExamStarted = false;
    if (window.__aiStopAdminVoice) window.__aiStopAdminVoice();
    if (window.__aiStopAudioMonitoring) window.__aiStopAudioMonitoring();

    // Record WHY the exam ended, so the backend can permanently
    // block this student from re-attempting this exam when it was
    // a violation, while still allowing normal completed exams to
    // just show a "already submitted" message instead.
    const form = document.querySelector('form[action*="/submit"]') || document.forms[0];
    if (form) {
      let reasonInput = form.querySelector('input[name="termination_reason"]');
      if (!reasonInput) {
        reasonInput = document.createElement('input');
        reasonInput.type = 'hidden';
        reasonInput.name = 'termination_reason';
        form.appendChild(reasonInput);
      }
      reasonInput.value = violationType;
    }

    logViolation(violationType, violationMessage);
    endingMsg.textContent = reasonLabel + ' Submitting your exam automatically...';
    endingOverlay.style.display = 'flex';

    // Start saving immediately; no artificial delay.
    if (window.__aiStopExamSubmit) {
      window.__aiStopExamSubmit();
    } else if (form) {
      form.submit();
    }
  }


  // =====================================================
  // SOUND & MICROPHONE CHECK (must pass before the exam can start)
  // A web page cannot read the computer's volume setting. So it plays a
  // short beep through the speakers and measures how loudly the microphone
  // hears it: that proves the volume is turned up and the microphone works.
  // The check repeats by itself, so as soon as the student raises the volume
  // the step turns green. Needs speakers (headphones will not pass).
  // =====================================================
  (function soundCheck(){
    const box = document.getElementById('ai-sc');
    const scBtn = document.getElementById('ai-sc-btn');
    const volRow = document.getElementById('sc-vol'), micRow = document.getElementById('sc-mic');
    const volT = document.getElementById('sc-vol-t'), micT = document.getElementById('sc-mic-t');
    const meter = document.getElementById('sc-meter-i'), devSel = document.getElementById('sc-dev');
    const pop = document.getElementById('ai-sc-pop'), popT = document.getElementById('ai-sc-pop-t'), popM = document.getElementById('ai-sc-pop-m');
    document.getElementById('ai-sc-pop-ok').addEventListener('click', () => { pop.classList.remove('show'); popDismissedAt = Date.now(); });
    let popDismissedAt = 0;
    let required = true, minToneDb = -40;
    let passed = false, running = false, volOk = false, micOk = false;
    let stream = null, ctx = null, an = null, timer = null, osc = null, gain = null;
    const TONE_HZ = 1000;

    function setRow(row, state, ic){ row.className = 'sc-row ' + state; row.querySelector('.sc-ic').textContent = ic; }
    function showPop(title, msg){ popT.textContent = title; popM.textContent = msg; pop.classList.add('show'); }
    function hidePop(){ pop.classList.remove('show'); }

    // keep the Start button locked until both checks pass
    function lockStart(msg){ startBtn.disabled = true; startBtn.textContent = msg || 'Complete the sound check to start'; }
    function unlockStart(){ startBtn.disabled = false; startBtn.innerHTML = 'Enter Fullscreen &amp; Start Exam'; }

    // single-frequency level in dBFS (Goertzel)
    function toneDb(buf, sr, hz){
      const n = buf.length, k = Math.round(n * hz / sr), w = 2 * Math.PI * k / n, c = 2 * Math.cos(w);
      let s0 = 0, s1 = 0, s2 = 0;
      for (let i = 0; i < n; i++) { s0 = buf[i] + c * s1 - s2; s2 = s1; s1 = s0; }
      const p = s1 * s1 + s2 * s2 - c * s1 * s2;
      const amp = 2 * Math.sqrt(Math.max(p, 0)) / n;
      return 20 * Math.log10(amp + 1e-9);
    }
    function rms(buf){ let a = 0; for (let i = 0; i < buf.length; i++) a += buf[i] * buf[i]; return Math.sqrt(a / buf.length); }

    function cleanup(){
      running = false;
      if (timer) { clearInterval(timer); timer = null; }
      try { if (osc) osc.stop(); } catch(e) {}
      try { if (stream) stream.getTracks().forEach(t => t.stop()); } catch(e) {}
      try { if (ctx) ctx.close(); } catch(e) {}
      stream = ctx = an = osc = gain = null;
      meter.style.width = '0';
    }

    async function begin(){
      cleanup();
      volOk = micOk = false; passed = false; lockStart();
      setRow(volRow, 'run', '1'); setRow(micRow, '', '2');
      volT.textContent = 'Playing a beep… keep your computer volume at 100% and use speakers (not headphones).';
      scBtn.disabled = true; scBtn.textContent = 'Checking…';
      try {
        const id = devSel.value;
        stream = await navigator.mediaDevices.getUserMedia({audio: Object.assign(
          {echoCancellation:false, noiseSuppression:false, autoGainControl:false},
          id ? {deviceId:{exact:id}} : {})});
        // list microphones (labels only appear after permission is given)
        try {
          const devs = (await navigator.mediaDevices.enumerateDevices()).filter(d => d.kind === 'audioinput');
          if (devs.length > 1) {
            const cur = (stream.getAudioTracks()[0].getSettings() || {}).deviceId || id;
            devSel.innerHTML = '';
            devs.forEach(d => { const o = document.createElement('option'); o.value = d.deviceId; o.textContent = d.label || 'Microphone'; if (d.deviceId === cur) o.selected = true; devSel.appendChild(o); });
            devSel.style.display = 'block';
          }
        } catch(e) {}
        ctx = new (window.AudioContext || window.webkitAudioContext)();
        await ctx.resume();
        an = ctx.createAnalyser(); an.fftSize = 4096; an.smoothingTimeConstant = 0;
        ctx.createMediaStreamSource(stream).connect(an);
      } catch (e) {
        console.warn('Sound check mic error:', e);
        cleanup();
        setRow(volRow, 'bad', '!');
        volT.textContent = 'The microphone could not be opened. Allow microphone access (and pick the right microphone), then press the button again.';
        scBtn.disabled = false; scBtn.textContent = 'Try again';
        showPop('Microphone not available', 'Please allow microphone access in the browser and make sure a microphone is connected. Then press "Try again".');
        return;
      }
      running = true; scBtn.textContent = 'Checking…';
      runVolumePhase();
    }

    function runVolumePhase(){
      const sr = ctx.sampleRate, buf = new Float32Array(an.fftSize);
      let bursts = 0, goodInRow = 0, failBursts = 0, lastDb = -120, phaseStart = 0, bestInBurst = -120, noiseDb = -120, state = 'quiet';
      // Each cycle: 0.5 s silence (measure background) -> 0.8 s beep -> 0.4 s rest
      function playBeep(){
        try {
          osc = ctx.createOscillator(); gain = ctx.createGain();
          osc.type = 'sine'; osc.frequency.value = TONE_HZ;
          gain.gain.setValueAtTime(0.0001, ctx.currentTime);
          gain.gain.linearRampToValueAtTime(0.9, ctx.currentTime + 0.05);
          gain.gain.setValueAtTime(0.9, ctx.currentTime + 0.75);
          gain.gain.linearRampToValueAtTime(0.0001, ctx.currentTime + 0.8);
          osc.connect(gain); gain.connect(ctx.destination);
          osc.start(); osc.stop(ctx.currentTime + 0.82);
        } catch(e) {}
      }
      phaseStart = Date.now(); state = 'quiet'; noiseDb = -120;
      timer = setInterval(() => {
        if (!running) return;
        an.getFloatTimeDomainData(buf);
        const t = Date.now() - phaseStart;
        const db = toneDb(buf, sr, TONE_HZ);
        meter.style.width = Math.min(100, Math.max(0, (db + 70) * 100 / 55)) + '%';
        if (state === 'quiet') {
          noiseDb = Math.max(noiseDb, db);
          if (t > 500) { state = 'beep'; phaseStart = Date.now(); bestInBurst = -120; playBeep(); }
        } else if (state === 'beep') {
          if (t > 150) bestInBurst = Math.max(bestInBurst, db);
          if (t > 950) {
            state = 'rest'; phaseStart = Date.now(); bursts++;
            lastDb = bestInBurst;
            const heard = bestInBurst >= minToneDb && (bestInBurst - noiseDb) >= 10;
            if (heard) { goodInRow++; failBursts = 0; } else { goodInRow = 0; failBursts++; }
            const shown = bestInBurst < -100 ? 'silence' : Math.round(bestInBurst) + ' dB';
            if (goodInRow >= 2) {
              volOk = true; setRow(volRow, 'ok', '✔');
              volT.textContent = 'Volume is high enough (heard: ' + shown + '). Thank you.';
              hidePop(); clearInterval(timer); timer = null; runMicPhase(); return;
            }
            setRow(volRow, 'bad', '!');
            volT.textContent = 'The beep was too quiet (heard: ' + shown + ', need ' + minToneDb + ' dB). Turn your computer volume up to 100%, remove headphones, and wait — it re-checks by itself.';
            if (failBursts >= 2 && Date.now() - popDismissedAt > 15000 && !pop.classList.contains('show')) {
              showPop('Set your volume to 100%', 'Your computer volume is too low (or headphones are connected). Raise the system volume to 100% and use the speakers. The check repeats automatically and will continue as soon as the volume is high enough.');
            }
          }
        } else if (state === 'rest') {
          if (t > 450) { state = 'quiet'; phaseStart = Date.now(); noiseDb = -120; }
        }
      }, 100);
    }

    function runMicPhase(){
      setRow(micRow, 'run', '2');
      micT.textContent = 'Say “I am ready” aloud in your normal voice.';
      const buf = new Float32Array(an.fftSize);
      let loud = 0, start = Date.now(), nagged = false;
      timer = setInterval(() => {
        if (!running) return;
        an.getFloatTimeDomainData(buf);
        const lv = rms(buf);
        meter.style.width = Math.min(100, lv * 100 / 0.12 * 1.0) + '%';
        if (lv >= 0.012) loud++;
        if (loud >= 8) {   // about 0.8 s of real speech in total
          micOk = true; setRow(micRow, 'ok', '✔');
          micT.textContent = 'Microphone works. Thank you.';
          hidePop(); clearInterval(timer); timer = null; finish(); return;
        }
        if (Date.now() - start > 10000 && !nagged) {
          nagged = true;
          micT.textContent = 'We cannot hear you. Speak louder or closer, check the microphone choice below, or raise the microphone volume in your computer’s Sound settings.';
          setRow(micRow, 'bad', '!');
          showPop('We cannot hear you', 'Say “I am ready” aloud. If nothing is picked up, choose the correct microphone from the list or increase the microphone volume in Windows Sound settings. The check keeps listening.');
        }
      }, 100);
    }

    function finish(){
      passed = volOk && micOk;
      const chosen = devSel.style.display !== 'none' ? devSel.value : '';
      cleanup();
      if (passed) {
        window.__aiAudioDeviceId = chosen || undefined;
        scBtn.textContent = 'Sound check passed ✔'; scBtn.disabled = true; scBtn.style.background = '#16a34a';
        unlockStart();
      }
    }

    devSel.addEventListener('change', () => { if (!passed) begin(); });
    scBtn.addEventListener('click', begin);

    // Safety net if the exam is started some other way
    window.__aiSoundCheckPassed = () => !required || passed;
    window.__aiSoundCheckPopup = () => showPop('Sound check required', 'Complete the sound check first: computer volume at 100% (speakers) and a working microphone. The Start button unlocks automatically when both pass.');

    fetch('/student/exam/preflight-config', {credentials:'same-origin', cache:'no-store'})
      .then(r => r.ok ? r.json() : {})
      .then(c => {
        required = !(c && c.require_volume === false);
        if (c && typeof c.min_tone_db === 'number') minToneDb = c.min_tone_db;
      })
      .catch(() => {})
      .finally(() => {
        if (!required) { unlockStart(); return; }
        box.style.display = 'block';
        lockStart();
        if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
          setRow(volRow, 'bad', '!'); volT.textContent = 'This browser cannot use the microphone. Please open the exam in Microsoft Edge or Chrome.';
          scBtn.disabled = true;
        }
      });
  })();

  startBtn.addEventListener('click', async () => {
    if (window.__aiSoundCheckPassed && !window.__aiSoundCheckPassed()) { if (window.__aiSoundCheckPopup) window.__aiSoundCheckPopup(); return; }
    startBtn.disabled = true;
    startBtn.textContent = 'Requesting camera access...';

    // Camera/mic permission MUST happen before entering fullscreen.
    // Browsers automatically force-exit fullscreen the instant they
    // need to show a permission popup (it can't render inside a
    // fullscreen page) — if we were already in fullscreen at this
    // point, that forced exit would immediately look like the
    // student violated fullscreen mode and auto-submit their exam
    // with zero answers before they even got a chance to click
    // "Allow". Requesting permission first, while still in the
    // normal (non-fullscreen) page, avoids that entirely.
    if (window.__aiStartMonitoring) {
      try {
        await window.__aiStartMonitoring();
      } catch (e) {
        console.error('Monitoring start error:', e);
      }
    }

    startBtn.textContent = 'Entering fullscreen...';

    try { await enterFullscreen(); } catch(e) { console.warn(e); }

    startOverlay.style.display = 'none';
    examStarted = true;
    window.__aiExamStarted = true;
    examStartGraceUntil = Date.now() + 2500;
    hardLock = true;
    tryKeyboardLock();
    fetch('/student/exam/' + encodeURIComponent(examId) + '/begin', {method:'POST', credentials:'same-origin'})
      .then(r => r.json()).then(d => { if (d && typeof d.remaining_seconds === 'number') window.__aiRemainingSeconds = d.remaining_seconds; })
      .catch(() => {});

    // Resume audio analysis again right after, in case the context
    // was still suspended after creation — same click's activation
    // window, extra safety net.
    if (window.__aiResumeAudioContext) {
      try { window.__aiResumeAudioContext(); } catch(e) { console.warn(e); }
    }
  });

  function handleFsChange(){
    if (!examStarted || examEnding) return;
    if (Date.now() < examStartGraceUntil) return;
    if (!isFullscreen()) {
      autoEndExam(
        'You exited fullscreen mode.',
        'fullscreen_exit',
        'Student exited fullscreen mode — exam auto-submitted'
      );
    }
  }
  document.addEventListener('fullscreenchange', handleFsChange);
  document.addEventListener('webkitfullscreenchange', handleFsChange);
  document.addEventListener('msfullscreenchange', handleFsChange);

  document.addEventListener('visibilitychange', () => {
    if (!examStarted || examEnding) return;
    if (Date.now() < examStartGraceUntil) return;
    if (document.hidden) {
      // Re-check shortly after instead of acting on the very first
      // event: a genuine tab switch/minimize stays hidden, while the
      // fullscreen-transition blip this used to misfire on corrects
      // itself within a frame or two.
      setTimeout(() => {
        if (!examStarted || examEnding) return;
        if (!document.hidden) return;
        logTabViolation('Student switched tabs or minimized the window — exam auto-submitted');
        autoEndExam(
          'You switched tabs or windows.',
          'tab_switch_autoend',
          'Student switched tabs/windows — exam auto-submitted'
        );
      }, 500);
    }
  });

  window.addEventListener('blur', () => {
    if (!examStarted || examEnding) return;
    if (Date.now() < examStartGraceUntil) return;
    window.__aiRegisterWarning('window_blur', 'Exam window lost focus');
  });

  document.addEventListener('contextmenu', e => e.preventDefault());

  // =====================================================
  // PASSWORD-AWARE KEYBOARD LOCKDOWN
  // The keyboard stays blocked during the exam. Authorized users may type
  // the teacher's unlock password; the browser sends the candidate to the
  // server for validation, so the real password is never embedded in this
  // page. All normal keys remain blocked until the server confirms it.
  // =====================================================
  let keyboardStatusEl = document.getElementById('ai-keyboard-status');
  let resultLockOverlay = null;

  function setKeyboardUnlocked(){
    keyboardUnlocked = true;
    resultLocked = false;
    unlockBuffer = '';
    if (keyboardStatusEl){
      keyboardStatusEl.textContent = 'Keyboard: Unlocked';
      keyboardStatusEl.classList.add('unlocked');
    }

    const resultPill = document.getElementById('result-keyboard-pill');
    if (resultPill){
      resultPill.textContent = '🔓 Keyboard: Unlocked';
      resultPill.classList.add('unlocked');
    }
    const resultStatus = document.getElementById('result-unlock-status');
    if (resultStatus){
      resultStatus.textContent = 'Status: Unlocked. Keyboard is available.';
      resultStatus.style.color = '#86efac';
    }
    const resultButton = document.getElementById('result-unlock-btn');
    if (resultButton){
      resultButton.textContent = 'Unlocked';
      resultButton.disabled = true;
    }
    const resultPanel = document.getElementById('result-unlock-panel');
    if (resultPanel) resultPanel.style.borderColor = 'rgba(74,222,128,.45)';

    if (resultLockOverlay) resultLockOverlay.remove();
    if (isFullscreen() && document.exitFullscreen) {
      document.exitFullscreen().catch(()=>{});
    }
  }

  window.__aiShowResultLock = function(){
    examStarted = false;
    examEnding = false;
    resultLocked = true;
    keyboardUnlocked = false;
    unlockBuffer = '';

    // Remove a prior generated lock overlay, then add only a non-blocking
    // status banner. The actual teacher unlock controls below the result
    // must remain clickable.
    if (resultLockOverlay) resultLockOverlay.remove();
    resultLockOverlay = document.createElement('div');
    resultLockOverlay.id = 'ai-result-lock-overlay';
    resultLockOverlay.innerHTML = `
      <div class="ai-result-lock-box">
        <div class="ai-result-lock-icon">🔒</div>
        <h2>Exam Completed</h2>
        <p>Your result is displayed below.</p>
        <p><strong>Keyboard is locked until teacher unlock.</strong></p>
        <p class="ai-result-lock-small">Use the Teacher Unlock panel below to enter the authorized password.</p>
      </div>`;
    document.body.appendChild(resultLockOverlay);

    keyboardStatusEl = document.getElementById('ai-keyboard-status');
    if (!keyboardStatusEl) {
      keyboardStatusEl = document.createElement('div');
      keyboardStatusEl.id = 'ai-keyboard-status';
      document.body.appendChild(keyboardStatusEl);
    }
    keyboardStatusEl.textContent = 'Keyboard: Locked';
    keyboardStatusEl.classList.remove('unlocked');

    // The result template's script does not execute when the page is inserted
    // into the same document by the AJAX submit path, so wire the visible
    // unlock panel here as well.
    const input = document.getElementById('result-unlock-password');
    const button = document.getElementById('result-unlock-btn');
    const status = document.getElementById('result-unlock-status');

    async function unlockResultKeyboard(){
      const password = input ? input.value : '';
      if (!password){
        if (status) status.textContent = 'Status: Enter the teacher password first.';
        if (input) input.focus();
        return;
      }
      if (button) { button.disabled = true; button.textContent = 'Checking...'; }
      if (status) status.textContent = 'Status: Checking password...';

      try {
        const response = await fetch('/student/exam/keyboard-unlock', {
          method: 'POST',
          headers: {'Content-Type':'application/json'},
          credentials: 'same-origin',
          body: JSON.stringify({password, exam_id: examId})
        });
        const data = await response.json();
        if (data && data.unlocked) {
          if (input) input.value = '';
          setKeyboardUnlocked();
        } else {
          if (status) {
            status.textContent = 'Status: Incorrect password.';
            status.style.color = '#fbbf24';
          }
          if (input) input.select();
        }
      } catch (e) {
        console.error('Result unlock error:', e);
        if (status) {
          status.textContent = 'Status: Could not verify the password.';
          status.style.color = '#fbbf24';
        }
      } finally {
        if (button && !keyboardUnlocked) {
          button.disabled = false;
          button.textContent = 'Unlock';
        }
      }
    }

    if (button) {
      button.onclick = unlockResultKeyboard;
    }
    if (input) {
      input.onkeydown = (e) => {
        if (e.key === 'Enter') {
          e.preventDefault();
          unlockResultKeyboard();
        }
      };
      setTimeout(() => input.focus(), 80);
    }

    if (!isFullscreen()) {
      const note = resultLockOverlay.querySelector('.ai-result-lock-small');
      if (note) note.textContent = 'Use the Teacher Unlock panel below to enter the authorized password.';
    }
  };

  function checkKeyboardPassword(){
    if ((!examStarted && !resultLocked) || keyboardUnlocked || !unlockBuffer) return;
    const candidate = unlockBuffer;
    fetch('/student/exam/keyboard-unlock', {
      method: 'POST',
      headers: {'Content-Type':'application/json'},
      body: JSON.stringify({password: candidate, exam_id: examId})
    })
      .then(r => r.json())
      .then(data => {
        if (data && data.unlocked) setKeyboardUnlocked();
        else unlockBuffer = '';
      })
      .catch(() => { unlockBuffer = ''; });
  }

  // =====================================================
  // TOTAL PHYSICAL-KEYBOARD LOCK
  // From the moment the student presses Start, EVERY key is swallowed - there
  // is no hidden password buffer any more. After the exam the student gets the
  // ON-SCREEN keyboard page (see KEYBOARD_GATE_SCRIPT) to enter the unlock
  // password with the mouse only.
  // =====================================================
  let hardLock = false;
  function tryKeyboardLock(){
    // Chromium (Edge/Chrome) in fullscreen: also capture keys such as Esc,
    // Alt+Tab and the Windows key where the OS allows it. Best effort.
    try{
      if (navigator.keyboard && navigator.keyboard.lock) {
        navigator.keyboard.lock().catch(()=>{});
      }
    }catch(e){}
  }
  document.addEventListener('fullscreenchange', () => { if (hardLock && isFullscreen()) tryKeyboardLock(); });

  function keyboardLockdown(e){
    if (!(examStarted || hardLock)) return;
    e.preventDefault();
    e.stopImmediatePropagation();
    e.stopPropagation();
    return false;
  }
  ['keydown','keypress','keyup'].forEach(t => {
    window.addEventListener(t, keyboardLockdown, true);
    document.addEventListener(t, keyboardLockdown, true);
  });
  ['paste','copy','cut'].forEach(t => document.addEventListener(t, e => {
    if (examStarted || hardLock) { e.preventDefault(); }
  }, true));

  // Block the browser Back button during/after the exam.
  try { history.pushState(null, '', location.href); } catch(e) {}
  window.addEventListener('popstate', () => {
    if (examStarted || hardLock) { try { history.pushState(null, '', location.href); } catch(e) {} }
  });
})();
</script>
"""



# ============================================================
# POST-EXAM KEYBOARD GATE (on-screen keyboard)
# ============================================================
# Shown right after an exam ends (submitted, time over, or terminated for
# malpractice) and on every student page until the student unlocks. The
# physical keyboard is completely swallowed; the unlock password is entered by
# clicking the on-screen keys with the mouse. The result is NEVER shown to the
# student - only the examiner can see it.

KEYBOARD_GATE_SCRIPT = r"""
<style>
#kb-gate{position:fixed;inset:0;z-index:2147483647;display:flex;align-items:center;justify-content:center;
  background:radial-gradient(1200px 700px at 15% 10%,rgba(124,92,255,.35),transparent 60%),
             radial-gradient(1000px 600px at 90% 95%,rgba(255,137,179,.22),transparent 60%),#070a14;
  font-family:'Segoe UI',system-ui,Arial,sans-serif;color:#eef0fb;user-select:none;-webkit-user-select:none;overflow:auto}
#kb-gate *{box-sizing:border-box}
#kb-card{width:min(880px,94vw);margin:18px;padding:26px 28px 24px;border-radius:22px;
  background:linear-gradient(180deg,rgba(26,31,56,.92),rgba(16,20,38,.94));
  border:1px solid rgba(157,133,255,.35);box-shadow:0 30px 80px rgba(0,0,0,.55),0 0 0 1px rgba(255,255,255,.04) inset}
#kb-head{display:flex;align-items:center;gap:16px;margin-bottom:6px}
#kb-lock{width:58px;height:58px;border-radius:16px;display:grid;place-items:center;font-size:30px;
  background:linear-gradient(135deg,#7c5cff,#ff89b3);box-shadow:0 10px 30px rgba(124,92,255,.45)}
#kb-head h1{margin:0;font-size:24px;letter-spacing:-.01em}
#kb-head p{margin:3px 0 0;color:#a9b0cf;font-size:13.5px}
#kb-sub{color:#c7ccea;font-size:14px;margin:12px 0 14px;line-height:1.55}
#kb-status{display:flex;align-items:center;gap:12px;padding:12px 14px;border-radius:14px;margin-bottom:14px;
  background:rgba(124,92,255,.10);border:1px solid rgba(157,133,255,.28)}
#kb-status.ok{background:rgba(74,222,128,.10);border-color:rgba(74,222,128,.40)}
#kb-status.warn{background:rgba(251,191,36,.10);border-color:rgba(251,191,36,.40)}
#kb-spin{width:22px;height:22px;border-radius:50%;border:3px solid rgba(255,255,255,.18);border-top-color:#9d85ff;animation:kbspin .8s linear infinite;flex:none}
#kb-status.ok #kb-spin,#kb-status.warn #kb-spin{animation:none;border-color:transparent;display:grid;place-items:center}
#kb-status.ok #kb-spin::after{content:"\2714";color:#4ade80;font-size:24px;margin-top:-4px}
#kb-status.ok #kb-status-text{color:#4ade80;font-size:15px}
#kb-status.warn #kb-spin::after{content:"!";color:#fbbf24;font-weight:800;font-size:18px;margin-top:-3px}
@keyframes kbspin{to{transform:rotate(360deg)}}
#kb-status-text{font-size:14px;font-weight:600}
#kb-status-detail{font-size:12.5px;color:#a9b0cf;margin-top:2px;font-weight:400}
#kb-bar{height:5px;border-radius:99px;background:rgba(255,255,255,.08);overflow:hidden;margin:-4px 0 14px}
#kb-bar i{display:block;height:100%;width:8%;border-radius:99px;background:linear-gradient(90deg,#7c5cff,#ff89b3);transition:width .6s ease}
#kb-display{display:flex;align-items:center;justify-content:center;gap:8px;min-height:54px;margin:4px 0 14px;padding:10px 14px;
  border-radius:14px;background:#0a0e1d;border:1px solid rgba(255,255,255,.12);letter-spacing:.2em;font:700 22px/1 'IBM Plex Mono',ui-monospace,monospace}
#kb-display.shake{animation:kbshake .4s}
@keyframes kbshake{0%,100%{transform:translateX(0)}20%{transform:translateX(-9px)}40%{transform:translateX(9px)}60%{transform:translateX(-6px)}80%{transform:translateX(6px)}}
#kb-display .dot{width:13px;height:13px;border-radius:50%;background:linear-gradient(135deg,#9d85ff,#ff89b3);box-shadow:0 0 10px rgba(157,133,255,.7)}
#kb-display .ph{color:#6c7494;font:500 14px 'Segoe UI',Arial,sans-serif;letter-spacing:0}
#kb-keys{display:flex;flex-direction:column;gap:9px;align-items:center}
.kb-row{display:flex;gap:8px;justify-content:center;flex-wrap:nowrap}
.kb-key{min-width:clamp(34px,5.4vw,58px);height:clamp(44px,6.2vh,56px);padding:0 10px;border-radius:12px;cursor:pointer;
  border:1px solid rgba(255,255,255,.14);background:linear-gradient(180deg,#232a4a,#1a2039);color:#eef0fb;font:700 17px 'Segoe UI',Arial,sans-serif;
  box-shadow:0 3px 0 rgba(0,0,0,.45);transition:transform .06s,background .15s,box-shadow .06s}
.kb-key:hover{background:linear-gradient(180deg,#2d3560,#212849)}
.kb-key:active{transform:translateY(2px);box-shadow:0 1px 0 rgba(0,0,0,.45)}
.kb-key.wide{min-width:clamp(80px,12vw,130px);font-size:14px}
.kb-key.danger{background:linear-gradient(180deg,#5a2431,#40192a);border-color:rgba(248,113,113,.4)}
#kb-unlock{margin-top:6px;min-width:min(420px,80vw);height:54px;font-size:17px;border:0;color:#fff;
  background:linear-gradient(135deg,#7c5cff,#ff6fa4);box-shadow:0 12px 30px rgba(124,92,255,.45)}
#kb-gate.locked .kb-key,#kb-gate.locked #kb-unlock{opacity:.38;cursor:not-allowed;pointer-events:none;filter:grayscale(.6)}
#kb-hint{margin-top:14px;text-align:center;color:#8d95b8;font-size:12.5px}
#kb-toast{position:fixed;top:18px;left:50%;transform:translateX(-50%);padding:10px 18px;border-radius:12px;background:#2c1616;
  border:1px solid #f87171;color:#fecaca;font:600 13.5px 'Segoe UI',Arial,sans-serif;z-index:2147483647;display:none;max-width:90vw;text-align:center}
#kb-modal{position:fixed;inset:0;z-index:2147483647;display:none;align-items:center;justify-content:center;background:rgba(3,5,12,.72);backdrop-filter:blur(4px)}
#kb-modal .box{width:min(430px,90vw);padding:26px;border-radius:18px;text-align:center;background:#171c33;border:1px solid rgba(248,113,113,.55);
  box-shadow:0 24px 70px rgba(0,0,0,.6)}
#kb-modal .ic{font-size:40px;margin-bottom:6px}
#kb-modal h2{margin:0 0 8px;font-size:20px;color:#fecaca}
#kb-modal p{margin:0 0 18px;color:#c7ccea;font-size:14px;line-height:1.55}
#kb-modal button{border:0;border-radius:12px;padding:11px 28px;font:700 14.5px 'Segoe UI',Arial,sans-serif;color:#fff;cursor:pointer;background:linear-gradient(135deg,#7c5cff,#ff6fa4)}
#kb-modal.good .box{border-color:rgba(74,222,128,.55)}#kb-modal.good h2{color:#86efac}
</style>
<div id="kb-gate" class="locked">
  <div id="kb-card">
    <div id="kb-head">
      <div id="kb-lock">&#128274;</div>
      <div><h1 id="kb-title">Keyboard Locked</h1><p id="kb-sub-head">Your examination session has ended</p></div>
    </div>
    <div id="kb-sub"></div>
    <div id="kb-status"><div id="kb-spin"></div><div><div id="kb-status-text">Checking your recording&hellip;</div><div id="kb-status-detail"></div></div></div>
    <div id="kb-bar"><i></i></div>
    <div id="kb-display"><span class="ph">Type the unlock password with the on-screen keys</span></div>
    <div id="kb-keys">
      <div class="kb-row" data-row="0"></div>
      <div class="kb-row" data-row="1"></div>
      <div class="kb-row" data-row="2"></div>
      <div class="kb-row" data-row="3"></div>
      <button class="kb-key" id="kb-unlock" type="button">&#128275; Unlock Keyboard</button>
    </div>
    <div id="kb-hint">The physical keyboard is disabled. Use only your mouse. Letters A&ndash;Z only.</div>
  </div>
</div>
<div id="kb-toast"></div>
<div id="kb-modal"><div class="box"><div class="ic" id="kb-modal-ic">&#9888;&#65039;</div><h2 id="kb-modal-title"></h2><p id="kb-modal-msg"></p><button id="kb-modal-ok" type="button">OK</button></div></div>
<script>
(() => {
  const CFG = __KB_CONFIG__;
  const gate = document.getElementById('kb-gate');
  const display = document.getElementById('kb-display');
  const statusBox = document.getElementById('kb-status');
  const statusText = document.getElementById('kb-status-text');
  const statusDetail = document.getElementById('kb-status-detail');
  const bar = document.querySelector('#kb-bar i');
  const toast = document.getElementById('kb-toast');
  const modal = document.getElementById('kb-modal');
  let typed = '';
  let ready = !!CFG.alreadyReady;
  let unlocking = false;
  let unlocked = false;
  let blockedUntil = 0;
  let lastToast = 0;

  document.getElementById('kb-sub').textContent = CFG.message || '';
  if (CFG.subjectName) {
    document.getElementById('kb-sub-head').textContent = CFG.subjectName + ' — exam ended';
  }

  // ---- hard physical keyboard lock -------------------------------------
  function swallow(e){
    if (unlocked) return;
    e.preventDefault(); e.stopImmediatePropagation(); e.stopPropagation();
    if (e.type === 'keydown' && Date.now() - lastToast > 2500) {
      lastToast = Date.now();
      showToast('Physical keyboard is locked. Use the on-screen keyboard with your mouse.');
    }
    return false;
  }
  ['keydown','keyup','keypress','beforeinput','textInput','compositionstart','compositionupdate','paste','copy','cut'].forEach(t => {
    window.addEventListener(t, swallow, true);
    document.addEventListener(t, swallow, true);
  });
  document.addEventListener('contextmenu', e => e.preventDefault(), true);
  document.addEventListener('selectstart', e => e.preventDefault(), true);
  document.addEventListener('dragstart', e => e.preventDefault(), true);
  try { history.pushState(null, '', location.href); } catch(e) {}
  window.addEventListener('popstate', () => { if (!unlocked) { try { history.pushState(null, '', location.href); } catch(e) {} } });

  function tryFullscreenAndLock(){
    const el = document.documentElement;
    const fs = document.fullscreenElement || document.webkitFullscreenElement;
    const lock = () => { try { if (navigator.keyboard && navigator.keyboard.lock) navigator.keyboard.lock().catch(()=>{}); } catch(e) {} };
    if (!fs && el.requestFullscreen) { el.requestFullscreen().then(lock).catch(lock); }
    else { lock(); }
  }
  gate.addEventListener('pointerdown', () => { if (!unlocked) tryFullscreenAndLock(); }, true);
  tryFullscreenAndLock();
  window.addEventListener('beforeunload', e => { if (!unlocked && !window.__kbAllowUnload) { e.preventDefault(); e.returnValue = ''; } });

  // ---- on-screen keyboard ----------------------------------------------
  const ROWS = ['QWERTYUIOP', 'ASDFGHJKL', 'ZXCVBNM'];
  ROWS.forEach((letters, i) => {
    const row = document.querySelector('.kb-row[data-row="' + i + '"]');
    letters.split('').forEach(ch => {
      const b = document.createElement('button');
      b.type = 'button'; b.className = 'kb-key'; b.textContent = ch; b.dataset.k = ch;
      b.tabIndex = -1;
      b.addEventListener('click', () => press(ch));
      row.appendChild(b);
    });
  });
  const last = document.querySelector('.kb-row[data-row="3"]');
  const back = document.createElement('button');
  back.type = 'button'; back.className = 'kb-key wide danger'; back.textContent = '⌫ Backspace'; back.tabIndex = -1;
  back.addEventListener('click', () => { if (!ready) return; typed = typed.slice(0, -1); render(); });
  const clear = document.createElement('button');
  clear.type = 'button'; clear.className = 'kb-key wide danger'; clear.textContent = 'Clear'; clear.tabIndex = -1;
  clear.addEventListener('click', () => { if (!ready) return; typed = ''; render(); });
  last.appendChild(back); last.appendChild(clear);
  document.getElementById('kb-unlock').tabIndex = -1;
  document.getElementById('kb-unlock').addEventListener('click', submitUnlock);

  function press(ch){
    if (!ready || unlocked) return;
    if (typed.length >= 40) return;
    typed += ch;
    render();
  }
  function render(){
    display.innerHTML = '';
    if (!typed) {
      const ph = document.createElement('span'); ph.className = 'ph';
      ph.textContent = ready ? 'Type the unlock password with the on-screen keys' : 'Waiting for your recording to finish uploading…';
      display.appendChild(ph); return;
    }
    for (let i = 0; i < typed.length; i++) { const d = document.createElement('i'); d.className = 'dot'; display.appendChild(d); }
  }
  function showToast(msg){
    toast.textContent = msg; toast.style.display = 'block';
    clearTimeout(showToast._t); showToast._t = setTimeout(() => { toast.style.display = 'none'; }, 2600);
  }
  function showModal(kind, title, msg, onOk){
    const m = modal;
    m.className = kind === 'good' ? 'good' : '';
    document.getElementById('kb-modal-ic').textContent = kind === 'good' ? '✅' : '⚠️';
    document.getElementById('kb-modal-title').textContent = title;
    document.getElementById('kb-modal-msg').textContent = msg;
    m.style.display = 'flex';
    const ok = document.getElementById('kb-modal-ok');
    ok.onclick = () => { m.style.display = 'none'; if (onOk) onOk(); };
  }

  async function submitUnlock(){
    if (!ready || unlocking || unlocked) return;
    if (Date.now() < blockedUntil) {
      showModal('bad', 'Too many attempts', 'Please wait ' + Math.ceil((blockedUntil - Date.now()) / 1000) + ' seconds before trying again.');
      return;
    }
    if (!typed) { showModal('bad', 'Enter the password', 'Click the letters on the on-screen keyboard to type the unlock password.'); return; }
    unlocking = true;
    try {
      const r = await fetch(CFG.unlockUrl, {
        method: 'POST', credentials: 'same-origin',
        headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({password: typed, exam_id: CFG.examId})
      });
      const d = await r.json().catch(() => ({}));
      if (d && d.unlocked) {
        unlocked = true;
        window.__kbAllowUnload = true;
        gate.classList.remove('locked');
        document.getElementById('kb-title').textContent = 'Keyboard Unlocked';
        document.getElementById('kb-lock').innerHTML = '&#128275;';
        showModal('good', 'Keyboard unlocked', 'Your keyboard is available again.', () => {
          if (CFG.redirectUrl && location.pathname !== CFG.redirectUrl) location.href = CFG.redirectUrl;
          else { const g = document.getElementById('kb-gate'); if (g) g.remove(); modal.style.display = 'none'; }
        });
        return;
      }
      typed = ''; render();
      display.classList.remove('shake'); void display.offsetWidth; display.classList.add('shake');
      if (r.status === 429 || (d && d.retry_after)) {
        blockedUntil = Date.now() + (d.retry_after || 30) * 1000;
        showModal('bad', 'Too many wrong attempts', 'The keyboard stays locked. Try again in ' + (d.retry_after || 30) + ' seconds.');
      } else if (d && d.reason === 'recording_pending') {
        showModal('bad', 'Please wait', 'Your exam recording is still being uploaded. The keyboard can be unlocked as soon as it finishes.');
      } else {
        showModal('bad', 'Incorrect password', 'The password you entered is wrong. The keyboard remains locked. Please try again.');
      }
    } catch (e) {
      showModal('bad', 'Could not verify', 'The server could not be reached. Check the connection and try again.');
    } finally { unlocking = false; }
  }

  // ---- recording status ------------------------------------------------
  const STEP_TEXT = {
    none:      ['Exam submitted', 'No recording was produced for this attempt.', 100],
    processing:['Uploading video to admin…', 'Receiving the last part of your exam video.', 25],
    assembling:['Uploading video to admin…', 'Preparing the video file.', 45],
    uploading: ['Uploading video to admin…', 'Sending it to the examiner. Please keep this window open.', 70],
    done:      ['\u2714 Video uploaded successfully to admin', 'Your recording has reached the examiner. You can now unlock the keyboard.', 100],
    failed:    ['Recording upload is still retrying', 'It continues in the background. You can unlock the keyboard now.', 100]
  };
  function setProgress(p){ bar.style.width = Math.max(6, Math.min(100, p)) + '%'; }
  function applyStatus(s){
    const st = s && s.state ? s.state : 'processing';
    const t = STEP_TEXT[st] || STEP_TEXT.processing;
    statusText.textContent = t[0];
    statusDetail.textContent = (s && s.detail) ? s.detail : t[1];
    setProgress(t[2]);
    statusBox.className = (st === 'done' || st === 'none') ? 'ok' : (st === 'failed' ? 'warn' : '');
    const nowReady = !!(s && s.ready);
    if (nowReady && !ready) { ready = true; gate.classList.remove('locked'); render(); }
  }
  async function pollStatus(){
    if (unlocked) return;
    try {
      const r = await fetch(CFG.statusUrl + '?t=' + Date.now(), {credentials: 'same-origin', cache: 'no-store'});
      if (r.ok) applyStatus(await r.json());
    } catch (e) {}
    if (!ready) setTimeout(pollStatus, 1500);
  }
  if (CFG.alreadyReady) {
    gate.classList.remove('locked');
    statusBox.style.display = 'none'; document.getElementById('kb-bar').style.display = 'none';
    render();
  } else {
    gate.classList.add('locked');
    render();
    pollStatus();
  }
})();
</script>
"""


EXAM_DONE_TEMPLATE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Exam Submitted</title>
<style>html,body{margin:0;height:100%;background:#070a14;color:#eef0fb;font-family:'Segoe UI',system-ui,Arial,sans-serif}</style>
</head>
<body>
__GATE__
</body>
</html>
"""


DASHBOARD_BACKGROUND_CSS = r"""
<style>
@import url('https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@500;600;700;800&family=IBM+Plex+Mono:wght@400;500;600&display=swap');
/* =====================================================
   EXAM SYSTEM — SHARED DESIGN SYSTEM (Light / Creative)
   Same variable names & class names as before — every
   existing template keeps working without any changes.
   ===================================================== */


:root {
  /* Dark theme — deep navy base with a bright violet/coral/teal
     accent trio for pop against the dark surfaces. */
  --bg: #0a0e1a;
  --surface: #141a2c;
  --surface-2: #1b2338;
  --border: rgba(255, 255, 255, 0.10);
  --text: #f1f0f7;
  --text-muted: #b7b3cc;
  --text-dim: #8b87a3;

  --accent: #9d85ff;
  --accent-2: #ff89b3;
  --accent-dim: rgba(157, 133, 255, 0.18);

  --success: #4ade80;
  --success-bg: rgba(74, 222, 128, 0.12);
  --success-border: rgba(74, 222, 128, 0.35);
  --danger: #f87171;
  --danger-bg: rgba(248, 113, 113, 0.12);
  --danger-border: rgba(248, 113, 113, 0.35);
  --warning: #fbbf24;

  --font-display: 'Space Grotesk', sans-serif;
  --font-body: -apple-system, BlinkMacSystemFont, 'Segoe UI', Arial, sans-serif;
  --font-mono: 'IBM Plex Mono', 'Courier New', monospace;

  --radius: 14px;
  --shadow-sm: 0 1px 3px rgba(0, 0, 0, 0.35);
  --shadow-md: 0 10px 30px rgba(157, 133, 255, 0.22);
}

* { box-sizing: border-box; }

html {
  /* FIX: solid fallback so the page can never render with a dark
     background under any caching/load-order edge case — the
     animated gradient blobs below sit on top of this. */
  background-color: #faf8f5;
}

body {
  margin: 0;
  background-color: var(--bg);
  color: var(--text);
  font-family: var(--font-body);
  line-height: 1.5;
  position: relative;
  overflow-x: hidden;
}

/* ===================== ANIMATED BACKGROUND ===================== */
/* Soft, slow-drifting gradient blobs behind everything — the
   "creative" depth layer. Fixed + behind content (z-index -1) so it
   never interferes with clicking/reading anything, and pure CSS so
   no template needs a script tag added. */
body::before,
body::after {
  content: "";
  position: fixed;
  z-index: -1;
  width: 560px;
  height: 560px;
  border-radius: 50%;
  filter: blur(130px);
  opacity: 0.16;
  pointer-events: none;
}
body::before {
  top: -160px;
  left: -120px;
  background: radial-gradient(circle, var(--accent), transparent 70%);
  animation: floatBlobA 22s ease-in-out infinite;
}
body::after {
  bottom: -180px;
  right: -140px;
  background: radial-gradient(circle, var(--accent-2), transparent 70%);
  animation: floatBlobB 26s ease-in-out infinite;
}
@keyframes floatBlobA {
  0%, 100% { transform: translate(0, 0) scale(1); }
  50% { transform: translate(60px, 40px) scale(1.08); }
}
@keyframes floatBlobB {
  0%, 100% { transform: translate(0, 0) scale(1); }
  50% { transform: translate(-50px, -30px) scale(1.1); }
}
@media (prefers-reduced-motion: reduce) {
  body::before, body::after { animation: none; }
}

a { color: var(--accent); text-decoration: none; }
a:hover { text-decoration: underline; }

h1, h2, h3 {
  font-family: var(--font-display);
  font-weight: 700;
  margin: 0 0 8px;
  letter-spacing: -0.01em;
}

/* ===================== NAVBAR ===================== */
.navbar {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: 16px 32px;
  background: var(--surface);
  border-bottom: 1px solid var(--border);
  position: sticky;
  top: 0;
  z-index: 50;
}
.navbar .brand {
  font-family: var(--font-display);
  font-weight: 700;
  font-size: 17px;
  letter-spacing: -0.01em;
  color: var(--text);
  display: flex;
  align-items: center;
  gap: 8px;
}
.navbar .brand .dot {
  width: 10px; height: 10px; border-radius: 50%;
  background: linear-gradient(135deg, var(--accent), var(--accent-2));
  box-shadow: 0 0 0 4px var(--accent-dim);
}
.navbar .nav-links { display: flex; gap: 22px; align-items: center; }
.navbar .nav-links a {
  color: var(--text-muted);
  font-size: 14px;
  font-weight: 600;
}
.navbar .nav-links a:hover { color: var(--text); text-decoration: none; }
.navbar .nav-links a.logout { color: var(--danger); }

/* ===================== LAYOUT ===================== */
.page {
  max-width: 880px;
  margin: 0 auto;
  padding: 48px 24px 100px;
}
.page.wide { max-width: 1100px; }

.eyebrow {
  font-family: var(--font-mono);
  font-size: 11.5px;
  letter-spacing: 0.08em;
  text-transform: uppercase;
  color: var(--accent);
  margin-bottom: 10px;
  font-weight: 600;
}
.page-header { margin-bottom: 36px; }
.page-header p.desc { color: var(--text-muted); font-size: 14.5px; margin-top: 6px; }

/* ===================== CARD ===================== */
.card {
  background: rgba(255, 255, 255, 0.72);
  backdrop-filter: blur(10px);
  -webkit-backdrop-filter: blur(10px);
  border: 1px solid rgba(124, 92, 255, 0.16);
  border-radius: var(--radius);
  padding: 28px;
  margin-bottom: 18px;
  box-shadow: 0 10px 30px rgba(124, 92, 255, 0.12);
  animation: cardIn 0.4s ease both;
  transform-style: preserve-3d;
  perspective: 800px;
  transition: transform 0.25s ease, box-shadow 0.25s ease;
}
.card:hover {
  transform: translateY(-5px);
  box-shadow: 0 16px 40px rgba(124, 92, 255, 0.20);
}
.card-compact { padding: 18px 22px; }

@keyframes cardIn {
  from { opacity: 0; transform: translateY(10px); }
  to { opacity: 1; transform: translateY(0); }
}
@media (prefers-reduced-motion: reduce) {
  .card { animation: none; }
}

/* ===================== FORMS ===================== */
.form-group { margin-bottom: 18px; }
.form-group label {
  display: block;
  font-size: 13px;
  font-weight: 700;
  color: var(--text-muted);
  margin-bottom: 6px;
  letter-spacing: 0.01em;
}
.form-group input,
.form-group select,
.form-group textarea {
  width: 100%;
  padding: 11px 14px;
  background: var(--bg);
  border: 1.5px solid var(--border);
  border-radius: 10px;
  color: var(--text);
  font-size: 14.5px;
  font-family: var(--font-body);
  transition: border-color .15s, box-shadow .15s;
}
.form-group input:focus,
.form-group select:focus,
.form-group textarea:focus {
  outline: none;
  border-color: var(--accent);
  box-shadow: 0 0 0 3px var(--accent-dim);
}
.form-row { display: flex; gap: 16px; }
.form-row .form-group { flex: 1; }

.auth-card {
  max-width: 400px;
  margin: 80px auto;
}
.auth-card h1 { font-size: 22px; }
.auth-card .switch { text-align: center; margin-top: 18px; font-size: 13.5px; color: var(--text-muted); }

/* ===================== BUTTONS ===================== */
.btn {
  display: inline-flex;
  align-items: center;
  justify-content: center;
  gap: 6px;
  padding: 12px 24px;
  border-radius: 10px;
  border: 1px solid transparent;
  font-size: 14.5px;
  font-weight: 700;
  font-family: var(--font-body);
  cursor: pointer;
  text-decoration: none;
  transition: transform .1s ease, box-shadow .15s ease, opacity .15s ease;
}
.btn:hover { text-decoration: none; }
.btn:active { transform: translateY(1px); }
.btn-primary {
  background: linear-gradient(135deg, var(--accent), #9b7bff);
  color: #fff;
  box-shadow: 0 4px 14px rgba(124, 92, 255, 0.35);
}
.btn-primary:hover { opacity: 0.92; box-shadow: 0 6px 18px rgba(124, 92, 255, 0.42); }
.btn-block { width: 100%; }
.btn-secondary { background: var(--surface); border-color: var(--border); color: var(--text); }
.btn-secondary:hover { border-color: var(--accent); color: var(--accent); }
.btn-danger { background: transparent; border-color: var(--danger-border); color: var(--danger); }
.btn-sm { padding: 7px 14px; font-size: 13px; border-radius: 8px; }

/* ===================== TABLE ===================== */
table { width: 100%; border-collapse: collapse; }
.table-card { background: var(--surface); border: 1px solid var(--border); border-radius: var(--radius); overflow: hidden; box-shadow: var(--shadow-sm); transition: box-shadow 0.25s ease; }
.table-card:hover { box-shadow: var(--shadow-md); }
th, td { text-align: left; padding: 13px 18px; border-bottom: 1px solid var(--border); font-size: 14px; }
th { color: var(--text-muted); font-weight: 700; font-size: 11.5px; text-transform: uppercase; letter-spacing: 0.05em; background: var(--surface-2); }
tr:last-child td { border-bottom: none; }
tbody tr:hover { background: var(--surface-2); }

/* ===================== BADGES / CODES ===================== */
.code-tag {
  font-family: var(--font-mono);
  font-size: 12.5px;
  background: var(--accent-dim);
  border: 1px solid var(--border);
  padding: 3px 9px;
  border-radius: 6px;
  color: var(--accent);
  letter-spacing: 0.02em;
  font-weight: 600;
}
.badge {
  display: inline-block;
  padding: 4px 11px;
  border-radius: 20px;
  font-size: 12px;
  font-weight: 700;
}
.badge-success { background: var(--success-bg); color: var(--success); border: 1px solid var(--success-border); }
.badge-danger { background: var(--danger-bg); color: var(--danger); border: 1px solid var(--danger-border); }
.badge-neutral { background: var(--surface-2); color: var(--text-muted); border: 1px solid var(--border); }

/* ===================== ALERTS (flash messages) ===================== */
.alert {
  padding: 13px 18px;
  border-radius: 10px;
  font-size: 14px;
  margin-bottom: 18px;
  border: 1px solid;
  font-weight: 500;
}
.alert-success { background: var(--success-bg); border-color: var(--success-border); color: #15803d; }
.alert-error { background: var(--danger-bg); border-color: var(--danger-border); color: #be2f47; }

/* ===================== STAT / EMPTY STATES ===================== */
.stat-row { display: flex; gap: 14px; margin-bottom: 24px; flex-wrap: wrap; }
.stat-box {
  flex: 1;
  min-width: 130px;
  background: var(--surface);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  padding: 18px 20px;
  box-shadow: var(--shadow-sm);
  transition: transform 0.2s ease, box-shadow 0.2s ease;
}
.stat-box:hover {
  transform: translateY(-3px) scale(1.015);
  box-shadow: var(--shadow-md);
}
.stat-box .value { font-family: var(--font-display); font-size: 26px; font-weight: 800; }
.stat-box .label { font-size: 12px; color: var(--text-muted); text-transform: uppercase; letter-spacing: 0.05em; margin-top: 4px; font-weight: 600; }
.stat-box.accent .value { color: var(--accent); }
.stat-box.success .value { color: var(--success); }
.stat-box.danger .value { color: var(--danger); }

.empty-state {
  text-align: center;
  padding: 60px 20px;
  color: var(--text-dim);
}
.empty-state .icon { font-size: 34px; margin-bottom: 10px; opacity: 0.75; }

/* ===================== LANDING PAGE (index.html) ===================== */
.hero {
  text-align: left;
  padding: 60px 0 20px;
  border-bottom: 1px solid var(--border);
  margin-bottom: 40px;
  position: relative;
}
.hero h1 {
  font-size: 36px;
  max-width: 600px;
  background: linear-gradient(120deg, var(--text) 40%, var(--accent));
  -webkit-background-clip: text;
  background-clip: text;
  -webkit-text-fill-color: transparent;
}
.hero p { color: var(--text-muted); font-size: 16px; max-width: 520px; margin-top: 10px; }

.role-grid { display: grid; grid-template-columns: repeat(3, 1fr); gap: 18px; }
.role-card {
  background: var(--surface);
  border: 1px solid var(--border);
  border-radius: var(--radius);
  padding: 26px 22px;
  box-shadow: var(--shadow-sm);
  transition: transform .15s ease, box-shadow .15s ease;
}
.role-card:hover { transform: translateY(-5px); box-shadow: var(--shadow-md); }
.role-card .tag { font-family: var(--font-mono); font-size: 11px; color: var(--accent); text-transform: uppercase; letter-spacing: 0.08em; font-weight: 600; }
.role-card h2 { font-size: 18px; margin-top: 8px; }
.role-card p { color: var(--text-muted); font-size: 13.5px; margin: 8px 0 18px; }
.role-card .links { display: flex; gap: 14px; font-size: 13.5px; font-weight: 600; }

@media (max-width: 720px) {
  .role-grid { grid-template-columns: 1fr; }
  .form-row { flex-direction: column; gap: 0; }
  .navbar { padding: 14px 18px; }
  .page { padding: 32px 16px 80px; }
  .hero h1 { font-size: 28px; }
}

/* Night-sky scenery — deep indigo gradient, a soft moon glow,
   a scattered starfield, dark rolling-hill silhouettes near the
   horizon, and one slow shooting star for a touch of delight.
   Injected directly into every page so it never depends on a
   separately-served/cached static file. */
body {
    background:
        radial-gradient(circle at 82% 10%, rgba(226,232,255,0.30), transparent 40%),
        url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='300' height='300' viewBox='0 0 300 300'%3E%3Cg fill='%23ffffff'%3E%3Ccircle cx='20' cy='30' r='1.4' opacity='0.8'/%3E%3Ccircle cx='80' cy='70' r='1' opacity='0.5'/%3E%3Ccircle cx='140' cy='20' r='1.6' opacity='0.7'/%3E%3Ccircle cx='190' cy='90' r='1' opacity='0.45'/%3E%3Ccircle cx='250' cy='40' r='1.3' opacity='0.6'/%3E%3Ccircle cx='40' cy='130' r='1' opacity='0.5'/%3E%3Ccircle cx='110' cy='160' r='1.5' opacity='0.7'/%3E%3Ccircle cx='170' cy='140' r='1' opacity='0.4'/%3E%3Ccircle cx='230' cy='170' r='1.4' opacity='0.65'/%3E%3Ccircle cx='280' cy='120' r='1' opacity='0.5'/%3E%3Ccircle cx='15' cy='210' r='1.2' opacity='0.55'/%3E%3Ccircle cx='70' cy='240' r='1' opacity='0.45'/%3E%3Ccircle cx='150' cy='220' r='1.6' opacity='0.75'/%3E%3Ccircle cx='210' cy='260' r='1' opacity='0.5'/%3E%3Ccircle cx='270' cy='230' r='1.3' opacity='0.6'/%3E%3Ccircle cx='100' cy='280' r='1' opacity='0.4'/%3E%3C/g%3E%3C/svg%3E"),
        url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='1440' height='320' viewBox='0 0 1440 320' preserveAspectRatio='none'%3E%3Cpath d='M0,170 C240,120 480,210 720,165 C960,120 1200,200 1440,150 L1440,320 L0,320 Z' fill='%232a2f52' opacity='0.65'/%3E%3C/svg%3E"),
        url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='1440' height='320' viewBox='0 0 1440 320' preserveAspectRatio='none'%3E%3Cpath d='M0,230 C220,190 420,255 720,220 C1000,185 1220,245 1440,205 L1440,320 L0,320 Z' fill='%23161a30' opacity='0.9'/%3E%3C/svg%3E"),
        linear-gradient(180deg, #0a0e1a 0%, #10142a 45%, #171b38 100%) !important;
    background-attachment: fixed, fixed, fixed, fixed, fixed !important;
    background-repeat: no-repeat, repeat, repeat-x, repeat-x, no-repeat;
    background-position: 0 0, 0 0, bottom, bottom, 0 0;
    background-size: auto, 300px 300px, 1440px 320px, 1440px 320px, auto;
    color: #f1f0f7 !important;
    position: relative;
    overflow-x: hidden;
}
/* A soft pulsing halo around the "moon" glow, and one slow
   shooting star that sweeps across every couple of minutes. */
body::before {
    content: "";
    position: fixed;
    z-index: -1;
    pointer-events: none;
    top: 6%;
    right: 12%;
    width: 220px;
    height: 220px;
    border-radius: 50%;
    background: radial-gradient(circle, rgba(226,232,255,0.22), transparent 70%);
    filter: blur(10px);
    animation: aiMoonPulse 8s ease-in-out infinite;
}
body::after {
    content: "";
    position: fixed;
    z-index: -1;
    pointer-events: none;
    top: 8%;
    left: -10%;
    width: 160px;
    height: 2px;
    background: linear-gradient(90deg, transparent, #ffffff, transparent);
    border-radius: 50%;
    transform: rotate(18deg);
    opacity: 0;
    animation: aiShootingStar 9s linear infinite;
    animation-delay: 3s;
}
@keyframes aiMoonPulse {
    0%, 100% { opacity: 0.7; transform: scale(1); }
    50% { opacity: 1; transform: scale(1.08); }
}
@keyframes aiShootingStar {
    0%   { transform: translate(0, 0) rotate(18deg); opacity: 0; }
    3%   { opacity: 1; }
    12%  { transform: translate(60vw, 30vh) rotate(18deg); opacity: 0; }
    100% { opacity: 0; }
}
@media (prefers-reduced-motion: reduce) {
    body::before, body::after { animation: none !important; }
}
/* Safety net: guarantees the dark glass-card look even on hand-built
   inline pages, or any element whose class merely contains "card".
   Kept intentionally flat (no tilt/perspective) — a clean lift and
   glow reads as polished without needing 3D transforms. */
[class*="card"] {
    background: rgba(20, 24, 42, 0.62) !important;
    backdrop-filter: blur(12px);
    -webkit-backdrop-filter: blur(12px);
    border: 1px solid rgba(157,133,255,0.28) !important;
    box-shadow: 0 10px 30px rgba(0,0,0,0.35) !important;
    transition: transform 0.25s ease, box-shadow 0.25s ease, border-color 0.25s ease;
}
[class*="card"]:hover {
    transform: translateY(-5px);
    border-color: rgba(157,133,255,0.50) !important;
    box-shadow: 0 18px 42px rgba(0,0,0,0.45), 0 0 0 1px rgba(157,133,255,0.15) !important;
}

</style>
"""




# ============================================================
# EXAM CLOCK, FORFEITS, DONE PAGE, LIVE SESSION LIST, STRAY-TEXT CLEANUP
# ============================================================
EXAM_BEGIN_TIMES = {}
EXAM_BEGIN_LOCK = threading.Lock()


@app.route("/student/exam/<exam_id>/begin", methods=["POST"])
@student_login_required
def exam_begin(exam_id):
    """Called when the student presses Start. The clock lives on the server so a
    page refresh can never give extra time."""
    if str(exam_id) != str(session.get("current_exam_id", "")):
        return jsonify({"success": False, "error": "Invalid exam"}), 403
    try:
        duration = int(session.get("current_exam_duration_minutes", 30) or 30)
    except (TypeError, ValueError):
        duration = 30
    key = _rec_key(session.get("student_id", ""), exam_id)
    with EXAM_BEGIN_LOCK:
        begun = EXAM_BEGIN_TIMES.setdefault(key, time.time())
    remaining = max(0, int(duration * 60 - (time.time() - begun)))
    return jsonify({"success": True, "remaining_seconds": remaining})


def _record_forfeit(student_id, student_name, student_email, exam_id, status_label):
    """Close an attempt whose time ran out while the student was away."""
    try:
        wb = load_database()
        subject_name = subject_code = ""
        for row in wb["Exams"].iter_rows(min_row=2, values_only=True):
            if row[0] == exam_id:
                subject_name, subject_code = row[3], row[4]
                break
        result_sheet, _details = _ensure_results_schema(wb)
        result_id = "R" + uuid.uuid4().hex[:10].upper()
        submitted_at = _now_local().strftime("%Y-%m-%d %H:%M:%S")
        _append_result_by_header(result_sheet, {
            "Result ID": result_id, "Student ID": student_id, "Student Name": student_name,
            "Student Email": student_email, "Exam ID": exam_id, "Subject Name": subject_name,
            "Subject Code": subject_code, "Total Questions": 0, "Correct Answers": 0,
            "Wrong Answers": 0, "Score": "0/0", "Percentage": 0, "Recording File": "",
            "Exam Status": status_label, "Unattempted Answers": 0, "Submitted At": submitted_at,
        })
        save_database(wb)
        wb.close()
    except Exception as exc:
        print("Forfeit record error:", exc)


def _render_exam_done(exam_id, subject_name, exam_status):
    """Page shown after an exam ends. NO score is shown - only the on-screen
    keyboard gate that must be unlocked with the examiner's password."""
    sid = session.get("student_id", "")
    cfg = {
        "examId": exam_id,
        "statusUrl": "/student/exam/" + str(exam_id) + "/recording-status",
        "unlockUrl": "/student/exam/keyboard-unlock",
        "redirectUrl": "/student/dashboard",
        "message": "Your exam has ended. Enter the unlock password on the on-screen keyboard to continue.",
        "subjectName": subject_name or "",
        "alreadyReady": _recording_ready(sid, exam_id),
    }
    gate = KEYBOARD_GATE_SCRIPT.replace("__KB_CONFIG__", json.dumps(cfg))
    resp = app.make_response(EXAM_DONE_TEMPLATE.replace("__GATE__", gate))
    resp.headers["Cache-Control"] = "no-store"
    return resp


@app.route("/internal/live-sessions")
def internal_live_sessions():
    """Token-protected list of students currently taking an exam. The admin
    server pulls this so the live wall works even if a push was missed."""
    if not LIVE_SYNC_TOKEN or request.headers.get("X-ExamGuard-Sync-Token", "") != LIVE_SYNC_TOKEN:
        return jsonify({"success": False, "error": "Unauthorized"}), 401
    sessions = []
    now = time.time()
    try:
        for name in os.listdir(LIVE_FRAMES_FOLDER):
            if not name.endswith(".json"):
                continue
            try:
                with open(os.path.join(LIVE_FRAMES_FOLDER, name), "r", encoding="utf-8") as fh:
                    data = json.load(fh)
            except Exception:
                continue
            age = now - float(data.get("last_seen", 0) or 0)
            if age > 30:
                continue
            data["age"] = round(age, 2)
            data.update(_live_violation_fields(data.get("student_id", "")))
            sessions.append(data)
    except Exception as exc:
        print("live-sessions error:", exc)
    return jsonify({"success": True, "sessions": sessions, "server_time": now})


STRAY_TEXT_CLEANUP = r"""
<script id="ai-stray-clean">
(function(){
  // Removes loose text such as "html" or ";;;(}}" that leaks into the page
  // when stylesheet/markup fragments are mis-parsed. Only text nodes made
  // purely of code punctuation or the bare word "html" are touched.
  var BAD = /^\s*(html|[;{}()\[\]\s]+)\s*$/i;
  function clean(){
    try{
      var w = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT, null);
      var drop = [], n;
      while ((n = w.nextNode())) {
        var p = n.parentNode && n.parentNode.nodeName;
        if (p === 'SCRIPT' || p === 'STYLE' || p === 'TEXTAREA' || p === 'NOSCRIPT') continue;
        if (n.nodeValue && n.nodeValue.trim() && BAD.test(n.nodeValue)) drop.push(n);
      }
      drop.forEach(function(t){ t.parentNode && t.parentNode.removeChild(t); });
    }catch(e){}
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', clean); else clean();
  setTimeout(clean, 400);
})();
</script>
"""



# ============================================================
# ZOOM LOCK (all pages): the page always stays at 100 %
# ============================================================
ZOOM_LOCK_SNIPPET = r"""<!--eg-zoom-lock--><script>
(function(){
  function stop(e){ try{ e.preventDefault(); e.stopPropagation(); }catch(x){} }
  // Ctrl + mouse wheel / touchpad pinch
  window.addEventListener('wheel', function(e){ if (e.ctrlKey || e.metaKey) stop(e); }, {passive:false, capture:true});
  // Ctrl + / Ctrl - / Ctrl 0 (also the number pad)
  window.addEventListener('keydown', function(e){
    if (!(e.ctrlKey || e.metaKey)) return;
    var k = e.key, c = e.code;
    if (k==='+'||k==='-'||k==='='||k==='_'||k==='0'||k==='Add'||k==='Subtract'||
        c==='Equal'||c==='Minus'||c==='Digit0'||c==='NumpadAdd'||c==='NumpadSubtract'||c==='Numpad0') stop(e);
  }, true);
  // Pinch on touch screens / Safari gestures
  ['gesturestart','gesturechange','gestureend'].forEach(function(n){ document.addEventListener(n, stop, {passive:false}); });
  document.addEventListener('touchmove', function(e){ if (e.touches && e.touches.length > 1) stop(e); }, {passive:false});
  // Zoom changed from the browser menu cannot be blocked, so cancel it by
  // scaling the page back to the size it had when it opened.
  var STEPS=[.25,.33,.5,.67,.75,.8,.9,1,1.1,1.25,1.5,1.75,2,2.5,3,4,5];
  function browserZoom(){
    var o=window.outerWidth, i=window.innerWidth;
    if(!o||!i) return 1;
    var r=o/i, best=1, d=9;
    STEPS.forEach(function(s){ var x=Math.abs(r-s)/s; if(x<d){d=x;best=s;} });
    return d<0.06 ? best : 1;
  }
  function compensate(){
    var z=browserZoom(), root=document.documentElement;
    if (Math.abs(z-1) < 0.02) { if (root.style.zoom) root.style.zoom = ''; }
    else { root.style.zoom = String(1/z); }
  }
  compensate();
  window.addEventListener('resize', compensate);
  setInterval(compensate, 400);
})();
</script>"""


@app.after_request
def eg_zoom_lock(response):
    try:
        if (request.method == "GET" and response.status_code == 200
                and "text/html" in (response.content_type or "") and not response.is_streamed):
            body = response.get_data(as_text=True)
            if "eg-zoom-lock" in body:
                return response
            body = body.replace('content="width=device-width, initial-scale=1"',
                                'content="width=device-width, initial-scale=1, maximum-scale=1, user-scalable=no"')
            import re as _re_zoom
            m = _re_zoom.search(r"<head[^>]*>", body, _re_zoom.I)
            if m:
                body = body[:m.end()] + ZOOM_LOCK_SNIPPET + body[m.end():]
            elif "</body>" in body:
                body = body.replace("</body>", ZOOM_LOCK_SNIPPET + "</body>")
            else:
                body = ZOOM_LOCK_SNIPPET + body
            response.set_data(body)
            response.headers["Content-Length"] = str(len(response.get_data()))
    except Exception as exc:
        print("[UI] zoom lock skipped:", exc)
    return response


# ============================================================
# 3D LOOK (all normal pages): depth layers, tilting glass cards, 3D buttons
# ------------------------------------------------------------
# Injected just before </body> so it works for every page without touching the
# templates. It is skipped on exam / live-monitoring / video pages so the
# camera, recording and live wall keep all the computer's power.
# ============================================================
EG_3D_SNIPPET = r"""<!--eg-3d-look--><style id="eg3d-css">
body::before,body::after{opacity:0 !important}
html{background-color:#0a0e1a;min-height:100%}body{min-height:100vh}
#eg3d-scene{position:fixed;inset:0;z-index:0;pointer-events:none;overflow:hidden;perspective:1100px;perspective-origin:50% 38%}
.eg3d-orb{position:absolute;transform:translate3d(calc(var(--mx,0)*var(--d,20)*1px),calc(var(--my,0)*var(--d,20)*1px),0)}
.eg3d-orb>i{display:block;width:100%;height:100%;border-radius:50%;
  background:radial-gradient(circle at 32% 26%,rgba(255,255,255,.60) 0,rgba(205,190,255,.38) 14%,rgba(124,92,255,.30) 42%,rgba(60,40,150,.10) 66%,rgba(20,10,70,0) 74%);
  box-shadow:inset -14px -18px 46px rgba(15,8,60,.60),0 34px 90px rgba(124,92,255,.22);
  animation:egFloat var(--t,14s) ease-in-out infinite alternate}
.eg3d-orb.pink>i{background:radial-gradient(circle at 32% 26%,rgba(255,255,255,.55) 0,rgba(255,200,225,.34) 14%,rgba(255,111,164,.26) 42%,rgba(120,30,90,.10) 66%,rgba(40,10,40,0) 74%);box-shadow:inset -14px -18px 46px rgba(60,8,40,.55),0 34px 90px rgba(255,111,164,.18)}
.eg3d-orb.blue>i{background:radial-gradient(circle at 32% 26%,rgba(255,255,255,.55) 0,rgba(190,225,255,.34) 14%,rgba(79,160,255,.26) 42%,rgba(20,60,130,.10) 66%,rgba(10,20,60,0) 74%);box-shadow:inset -14px -18px 46px rgba(8,25,70,.55),0 34px 90px rgba(79,160,255,.18)}
@keyframes egFloat{0%{transform:translate3d(0,0,0) scale(1)}100%{transform:translate3d(0,-34px,0) scale(1.05)}}
.eg3d-cube{position:absolute;width:var(--s,120px);height:var(--s,120px);transform-style:preserve-3d;
  animation:egSpin var(--t,32s) linear infinite;opacity:.85}
.eg3d-cube-wrap{position:absolute;transform:translate3d(calc(var(--mx,0)*var(--d,40)*1px),calc(var(--my,0)*var(--d,40)*1px),0);transform-style:preserve-3d}
.eg3d-cube b{position:absolute;inset:0;border:1px solid rgba(180,160,255,.42);background:linear-gradient(135deg,rgba(124,92,255,.10),rgba(255,111,164,.05));box-shadow:inset 0 0 24px rgba(124,92,255,.18)}
.eg3d-cube b:nth-child(1){transform:rotateY(0) translateZ(calc(var(--s,120px)/2))}
.eg3d-cube b:nth-child(2){transform:rotateY(90deg) translateZ(calc(var(--s,120px)/2))}
.eg3d-cube b:nth-child(3){transform:rotateY(180deg) translateZ(calc(var(--s,120px)/2))}
.eg3d-cube b:nth-child(4){transform:rotateY(270deg) translateZ(calc(var(--s,120px)/2))}
.eg3d-cube b:nth-child(5){transform:rotateX(90deg) translateZ(calc(var(--s,120px)/2))}
.eg3d-cube b:nth-child(6){transform:rotateX(-90deg) translateZ(calc(var(--s,120px)/2))}
@keyframes egSpin{from{transform:rotateX(-24deg) rotateY(0)}to{transform:rotateX(-24deg) rotateY(360deg)}}
.eg3d-ring{position:absolute;border-radius:50%;border:2px solid rgba(157,133,255,.34);box-shadow:0 0 30px rgba(124,92,255,.25),inset 0 0 30px rgba(124,92,255,.18);
  transform:rotateX(68deg);animation:egRing var(--t,18s) linear infinite}
@keyframes egRing{from{transform:rotateX(68deg) rotateZ(0)}to{transform:rotateX(68deg) rotateZ(360deg)}}

.eg3d-card{transform-style:preserve-3d;transition:transform .22s ease,box-shadow .25s ease;will-change:transform;animation:egCardIn .75s cubic-bezier(.2,.8,.2,1) backwards}
.eg3d-card.eg3d-hot{box-shadow:0 26px 60px rgba(0,0,0,.50),0 0 0 1px rgba(157,133,255,.38),0 0 44px rgba(124,92,255,.22) !important}
.eg3d-card>h1,.eg3d-card>h2,.eg3d-card>h3{transform:translateZ(26px)}
@keyframes egCardIn{from{opacity:0;transform:perspective(900px) rotateX(16deg) translateY(36px) scale(.97)}to{opacity:1;transform:perspective(900px) rotateX(0) translateY(0) scale(1)}}
.eg3d-glare{position:absolute;inset:0;border-radius:inherit;pointer-events:none;opacity:0;transition:opacity .25s ease;
  background:radial-gradient(circle at var(--gx,50%) var(--gy,0%),rgba(255,255,255,.17),rgba(255,255,255,0) 52%);z-index:2}
.eg3d-card.eg3d-hot>.eg3d-glare{opacity:1}

h1{filter:drop-shadow(0 6px 14px rgba(124,92,255,.32))}
button,.xbtn,input[type=submit],a.btn{transition:transform .15s ease,box-shadow .15s ease,filter .15s ease}
button:not(:disabled):hover,.xbtn:hover,input[type=submit]:hover,a.btn:hover{transform:translateY(-2px);filter:brightness(1.07);box-shadow:0 6px 0 -1px rgba(0,0,0,.38),0 16px 26px rgba(0,0,0,.38)}
button:not(:disabled):active,.xbtn:active,input[type=submit]:active,a.btn:active{transform:translateY(1px);box-shadow:0 1px 0 rgba(0,0,0,.4)}
tbody tr{transition:background .2s ease}
tbody tr:hover{background:rgba(157,133,255,.07)}
@media (prefers-reduced-motion:reduce){.eg3d-orb>i,.eg3d-cube,.eg3d-ring,.eg3d-card{animation:none !important}}
</style>
<script>
(function(){
  try{
    var reduce = window.matchMedia && matchMedia('(prefers-reduced-motion: reduce)').matches;
    var touch = window.matchMedia && matchMedia('(hover: none)').matches;
    var body = document.body; if(!body || document.getElementById('eg3d-scene')) return;

    // ---- background depth scene ----
    var scene = document.createElement('div'); scene.id = 'eg3d-scene';
    function orb(cls,l,t,sz,d,tm){ var o=document.createElement('div'); o.className='eg3d-orb '+cls;
      o.style.cssText='left:'+l+';top:'+t+';width:'+sz+'px;height:'+sz+'px;--d:'+d+';--t:'+tm+'s'; o.appendChild(document.createElement('i')); scene.appendChild(o); }
    orb('','6%','14%',150,34,13); orb('pink','82%','10%',110,22,16); orb('blue','90%','62%',190,46,12);
    orb('','12%','72%',210,50,15); orb('pink','46%','84%',90,18,11); orb('blue','70%','30%',70,14,17);
    function cube(l,t,s,d,tm){ var w=document.createElement('div'); w.className='eg3d-cube-wrap'; w.style.cssText='left:'+l+';top:'+t+';--d:'+d;
      var c=document.createElement('div'); c.className='eg3d-cube'; c.style.cssText='--s:'+s+'px;--t:'+tm+'s';
      for(var i=0;i<6;i++) c.appendChild(document.createElement('b')); w.appendChild(c); scene.appendChild(w); }

    // ---- neon tunnel (canvas, light: half resolution, ~30 fps, pauses when hidden) ----
    var cv=document.createElement('canvas'); cv.id='eg3d-tunnel';
    cv.style.cssText='position:absolute;inset:0;width:100%;height:100%;opacity:.9';
    scene.appendChild(cv);
    var shade=document.createElement('div');
    shade.style.cssText='position:absolute;inset:0;background:radial-gradient(ellipse at center,rgba(6,8,22,.55) 0%,rgba(6,8,22,.78) 62%,rgba(4,5,14,.93) 100%)';
    scene.appendChild(shade);
    (function(){
      var ctx=cv.getContext('2d'); if(!ctx) return;
      var W=0,H=0,t=0,last=0,cx=0,cy=0,tx=0,ty=0,run=true;
      function size(){ W=cv.width=Math.max(320,Math.floor(window.innerWidth/2)); H=cv.height=Math.max(200,Math.floor(window.innerHeight/2)); }
      size(); window.addEventListener('resize',size);
      if(!reduce && !touch) window.addEventListener('pointermove',function(e){ tx=(e.clientX/window.innerWidth-.5)*0.18; ty=(e.clientY/window.innerHeight-.5)*0.18; },{passive:true});
      document.addEventListener('visibilitychange',function(){ run=!document.hidden; if(run) requestAnimationFrame(frame); });
      var N=16, SPOKES=12;
      function frame(ts){
        if(!run) return;
        requestAnimationFrame(frame);
        if(ts-last<33) return; last=ts;
        var dt=reduce?0:0.011; t+=dt; cx+=(tx-cx)*.06; cy+=(ty-cy)*.06;
        ctx.fillStyle='#050714'; ctx.fillRect(0,0,W,H);
        var ox=W/2+cx*W, oy=H/2+cy*H, maxR=Math.hypot(W,H)*.62;
        ctx.lineCap='round';
        // spokes
        ctx.lineWidth=1;
        for(var s=0;s<SPOKES;s++){
          var a=s/SPOKES*Math.PI*2+t*.18;
          ctx.strokeStyle='rgba('+(s%2?'255,60,200':'40,200,255')+',.22)';
          ctx.beginPath(); ctx.moveTo(ox+Math.cos(a)*maxR*.05,oy+Math.sin(a)*maxR*.05); ctx.lineTo(ox+Math.cos(a)*maxR,oy+Math.sin(a)*maxR); ctx.stroke();
        }
        // rings (far to near)
        for(var i=N;i>=0;i--){
          var z=(i+(t*3)%1)/N;            // 0 near .. 1 far
          var p=Math.pow(1-z,2.2);        // perspective
          var r=maxR*p+4; if(r<3) continue;
          var alpha=Math.min(1,(1-z)*1.6)*.9;
          var hue=(i%2)?'255,60,200':'40,200,255';
          ctx.save(); ctx.translate(ox,oy); ctx.rotate(t*.35*(i%2?1:-1)+i*.12);
          ctx.lineWidth=Math.max(1,r*.018);
          ctx.strokeStyle='rgba('+hue+','+alpha.toFixed(3)+')';
          ctx.shadowColor='rgba('+hue+',.9)'; ctx.shadowBlur=10;
          ctx.beginPath();
          if(i%3===0){ // rounded square ring
            var q=r*.78; ctx.rect(-q,-q,q*2,q*2);
          } else { ctx.arc(0,0,r,0,Math.PI*2); }
          ctx.stroke();
          // pulsing dashes on circles
          if(i%3===1){ ctx.setLineDash([r*.18,r*.5]); ctx.lineDashOffset=-t*r*2; ctx.lineWidth=Math.max(1.5,r*.03); ctx.beginPath(); ctx.arc(0,0,r*.86,0,Math.PI*2); ctx.stroke(); ctx.setLineDash([]); }
          ctx.restore();
        }
        ctx.shadowBlur=0;
      }
      requestAnimationFrame(frame);
    })();
    body.insertBefore(scene, body.firstChild);

    // lift normal page content above the scene (keep fixed/absolute things as they are)
    Array.prototype.forEach.call(body.children, function(el){
      if (el === scene || /^(SCRIPT|STYLE|LINK)$/.test(el.tagName)) return;
      var cs = getComputedStyle(el);
      if (cs.position === 'static') { el.style.position = 'relative'; }
      if (cs.zIndex === 'auto') { el.style.zIndex = '1'; }
    });

    // ---- mouse parallax for the scene ----
    if (!reduce && !touch) {
      var mx=0,my=0,ticking=false;
      window.addEventListener('pointermove', function(e){
        mx=(e.clientX/window.innerWidth-.5)*2; my=(e.clientY/window.innerHeight-.5)*2;
        if(!ticking){ ticking=true; requestAnimationFrame(function(){ scene.style.setProperty('--mx',mx.toFixed(3)); scene.style.setProperty('--my',my.toFixed(3)); ticking=false; }); }
      }, {passive:true});
    }

    // ---- tilting glass cards ----
    function isCard(el){
      var r=el.getBoundingClientRect(); if(r.width<200||r.width>1300||r.height<90) return false;
      if(el.querySelector('video,canvas,iframe,textarea')) return false;
      var cs=getComputedStyle(el); var br=parseFloat(cs.borderTopLeftRadius)||0; if(br<10) return false;
      var hasShadow=cs.boxShadow&&cs.boxShadow!=='none'; var hasBorder=parseFloat(cs.borderTopWidth)>0;
      var bg=cs.backgroundColor; var hasBg=bg&&bg!=='rgba(0, 0, 0, 0)'&&bg!=='transparent';
      return hasBg&&(hasShadow||hasBorder);
    }
    var cards=[]; var all=document.querySelectorAll('div,section,form,article,main');
    for(var i=0;i<all.length&&i<600;i++){ var el=all[i]; if(el.closest('#eg3d-scene')||el.closest('.modal-bg')) continue;
      if(cards.some(function(c){return c.contains(el);})) continue; if(isCard(el)) cards.push(el); }
    cards.forEach(function(card,idx){
      card.classList.add('eg3d-card'); card.style.animationDelay=(idx*90)+'ms';
      if(getComputedStyle(card).position==='static') card.style.position='relative';
      var g=document.createElement('span'); g.className='eg3d-glare'; card.appendChild(g);
      if(reduce||touch) return;
      var raf=0;
      card.addEventListener('pointermove', function(e){
        var r=card.getBoundingClientRect(); var px=(e.clientX-r.left)/r.width, py=(e.clientY-r.top)/r.height;
        var max=r.width>700?2.2:7; var ry=(px-.5)*2*max, rx=-(py-.5)*2*max;
        if(raf) cancelAnimationFrame(raf);
        raf=requestAnimationFrame(function(){
          card.style.setProperty('transform','perspective(900px) rotateX('+rx.toFixed(2)+'deg) rotateY('+ry.toFixed(2)+'deg) translateZ(8px)','important');
          card.style.setProperty('--gx',(px*100).toFixed(0)+'%'); card.style.setProperty('--gy',(py*100).toFixed(0)+'%');
          card.classList.add('eg3d-hot');
        });
      });
      card.addEventListener('pointerleave', function(){
        if(raf) cancelAnimationFrame(raf); card.style.removeProperty('transform'); card.classList.remove('eg3d-hot');
      });
    });
  }catch(err){ if(window.console) console.warn('3D look skipped:', err); }
})();
</script>"""

_EG_3D_SKIP_PREFIXES = ("/student/exam", "/admin/live", "/internal", "/admin/recording-stream", "/admin/video", "/admin/voice")


@app.after_request
def eg_3d_effects(response):
    try:
        path = request.path or ""
        if (request.method == "GET" and response.status_code == 200
                and "text/html" in (response.content_type or "") and not response.is_streamed
                and not path.startswith(_EG_3D_SKIP_PREFIXES)):
            body = response.get_data(as_text=True)
            if "eg-3d-look" in body or "ai-camera-preview" in body:
                return response
            if "</body>" in body:
                body = body.replace("</body>", EG_3D_SNIPPET + "</body>", 1) if body.count("</body>") == 1 else body[:body.rfind("</body>")] + EG_3D_SNIPPET + body[body.rfind("</body>"):]
            else:
                body = body + EG_3D_SNIPPET
            response.set_data(body)
            response.headers["Content-Length"] = str(len(response.get_data()))
    except Exception as exc:
        print("[UI] 3D look skipped:", exc)
    return response



@app.after_request
def inject_student_ui(response):
    try:
        is_exam_page = (
            request.method == "GET"
            and request.path.startswith("/student/exam/")
            and request.path.count("/") >= 3
            and "text/html" in response.content_type
            and not response.is_streamed
        )

        if is_exam_page:
            body = response.get_data(as_text=True)

            if "ai-camera-preview" not in body and "</body>" in body:
                try:
                    _dur_for_script = int(session.get("current_exam_duration_minutes", 30) or 30)
                except (TypeError, ValueError):
                    _dur_for_script = 30
                _rec_script = (
                    EXAM_RECORDING_SCRIPT
                    .replace("__ICE_SERVERS_JSON__", json.dumps(_ice_servers()))
                    .replace("__EXAM_DURATION_MIN__", str(_dur_for_script))
                )
                body = body.replace("</body>", _rec_script + "</body>")

            if "ai-fs-start-overlay" not in body and "</body>" in body:
                body = body.replace("</body>", FULLSCREEN_AUTOEND_SCRIPT + "</body>")

            try:
                exam_duration = int(session.get("current_exam_duration_minutes", 30) or 30)
            except (TypeError, ValueError):
                exam_duration = 30
            timer_script = f"""<style>
#ai-exam-timer{{position:fixed;top:14px;right:18px;z-index:2147483400;min-width:180px;text-align:center;background:#072b10;border:2px solid #55ff66;color:#78ff8a;padding:8px 16px;border-radius:12px;font:800 26px 'Segoe UI',Arial,sans-serif;letter-spacing:.04em;box-shadow:0 0 20px rgba(70,255,100,.32);transition:color .2s,background .2s,border-color .2s,box-shadow .2s,transform .12s}}#ai-exam-timer-label{{display:block;font:800 10px 'Segoe UI',Arial,sans-serif;letter-spacing:.14em;text-transform:uppercase;margin-bottom:1px}}#ai-exam-timer-value{{display:block;line-height:1.05}}#ai-exam-timer.countdown{{animation:aiTimerBlink .75s steps(2,end) infinite;transform-origin:center}}@keyframes aiTimerBlink{{0%,100%{{filter:brightness(1);transform:scale(1)}}50%{{filter:brightness(1.35);transform:scale(1.04)}}}}
</style><div id="ai-exam-timer"><span id="ai-exam-timer-label">TIME LEFT</span><span id="ai-exam-timer-value">--:--</span></div><script>(()=>{{
const totalSeconds={exam_duration}*60;
let endAt=0;
let startedSeenAt=0;
let submitted=false;
let lastShownSecond=null;
let audioContext=null;
const el=document.getElementById('ai-exam-timer');
const val=document.getElementById('ai-exam-timer-value');

function ensureAudio(){{
  try{{
    if(!audioContext) audioContext=new (window.AudioContext||window.webkitAudioContext)();
    if(audioContext.state==='suspended') audioContext.resume().catch(()=>{{}});
    return audioContext;
  }}catch(e){{return null;}}
}}

function beep(frequency=880,duration=0.07,volume=0.035){{
  const ctx=ensureAudio();
  if(!ctx) return;
  try{{
    const osc=ctx.createOscillator();
    const gain=ctx.createGain();
    osc.type='sine';
    osc.frequency.value=frequency;
    gain.gain.setValueAtTime(volume,ctx.currentTime);
    gain.gain.exponentialRampToValueAtTime(0.001,ctx.currentTime+duration);
    osc.connect(gain);
    gain.connect(ctx.destination);
    osc.start();
    osc.stop(ctx.currentTime+duration);
  }}catch(e){{}}
}}

function timeoutBuzzer(){{
  beep(620,0.12,0.05);
  setTimeout(()=>beep(420,0.18,0.05),140);
}}

function tick(){{
  if(!window.__aiExamStarted) return;
  if(!endAt){{
    if(!startedSeenAt) startedSeenAt=Date.now();
    if(window.__aiRemainingSeconds===undefined && Date.now()-startedSeenAt<3000) return;
    const rem=(typeof window.__aiRemainingSeconds==='number')?window.__aiRemainingSeconds:totalSeconds;
    endAt=Date.now()+Math.min(totalSeconds,Math.max(1,rem))*1000;
  }}

  const left=Math.max(0,Math.ceil((endAt-Date.now())/1000));
  const ratio=totalSeconds>0?left/totalSeconds:0;
  const hue=Math.max(0,120*ratio);
  el.style.color=`hsl(${{hue}},100%,68%)`;
  el.style.borderColor=`hsl(${{hue}},100%,58%)`;
  el.style.background=`hsl(${{hue}},65%,13%)`;
  el.style.boxShadow=`0 0 20px hsla(${{hue}},100%,55%,.30)`;

  const m=Math.floor(left/60),s=left%60;
  val.textContent=String(m).padStart(2,'0')+':'+String(s).padStart(2,'0');

  // Last 30 seconds: visible blink + a small beep on every second.
  if(left<=30 && left>0){{
    el.classList.add('countdown');
    if(lastShownSecond!==left){{
      lastShownSecond=left;
      beep(left<=10?1040:880,0.07,0.032);
    }}
  }} else {{
    el.classList.remove('countdown');
    lastShownSecond=null;
  }}

  if(left<=0 && !submitted){{
    submitted=true;
    el.classList.add('countdown');
    timeoutBuzzer();
    // Immediate result-page submission with the answers currently
    // selected in the MCQ form. No normal Submit click is required.
    if(window.__aiSubmitExamAtTimeout){{
      window.__aiSubmitExamAtTimeout();
    }} else if(window.__aiStopExamSubmit){{
      window.__aiStopExamSubmit();
    }} else{{
      const f=document.querySelector('form');
      if(f) f.submit();
    }}
  }}
}}

tick();
setInterval(tick,250);
}})();</script>"""
            if "ai-exam-timer" not in body and "</body>" in body:
                body = body.replace("</body>", timer_script + "</body>")

            response.set_data(body)

        # Applied to every student page EXCEPT the live exam page
        # itself (kept plain/distraction-free while actually taking
        # the exam) — previously only 3 pages had it, missing the
        # results page and anything else.
        if (
            request.method == "GET"
            and not request.path.startswith("/student/exam/")
            and "text/html" in response.content_type
            and not response.is_streamed
        ):
            body = response.get_data(as_text=True)
            if session.get("kb_locked") and "kb-gate" not in body and "</body>" in body:
                _cfg = {
                    "examId": session.get("kb_locked_exam", ""),
                    "statusUrl": "/student/exam/" + str(session.get("kb_locked_exam", "")) + "/recording-status",
                    "unlockUrl": "/student/exam/keyboard-unlock",
                    "redirectUrl": "/student/dashboard",
                    "message": "Your exam is over. Unlock the keyboard to continue.",
                    "alreadyReady": _recording_ready(session.get("student_id", ""), session.get("kb_locked_exam", "")),
                }
                body = body.replace("</body>", KEYBOARD_GATE_SCRIPT.replace("__KB_CONFIG__", json.dumps(_cfg)) + "</body>")
            if "ai-stray-clean" not in body and "</body>" in body:
                body = body.replace("</body>", STRAY_TEXT_CLEANUP + "</body>")
            if "ai-dashboard-bg-applied" not in body:
                marker = "<!--ai-dashboard-bg-applied-->"
                if "</head>" in body:
                    body = body.replace("</head>", marker + DASHBOARD_BACKGROUND_CSS + "</head>")
                elif "<body" in body:
                    body = body.replace("<body", marker + DASHBOARD_BACKGROUND_CSS + "<body", 1)
                response.set_data(body)

    except Exception as e:
        print("UI injection error:", e)

    return response


def _bootstrap_for_wsgi():
    for fn in (initialize_database, _retry_pending_admin_syncs, ensure_recording_column,
               ensure_exam_status_column, ensure_violations_sheet):
        try:
            fn()
        except Exception as exc:
            print("[BOOT]", getattr(fn, "__name__", fn), "skipped:", exc)


if __name__ != "__main__":
    _bootstrap_for_wsgi()


if __name__ == "__main__":

    initialize_database()
    _retry_pending_admin_syncs()
    ensure_recording_column()
    ensure_exam_status_column()
    ensure_violations_sheet()

    import socket
    try:
        hostname = socket.gethostname()
        local_ip = socket.gethostbyname(hostname)
    except Exception:
        local_ip = "your-computer-ip"

    print("=" * 60)
    print("STUDENT EXAM SYSTEM")
    print("On this computer:      https://127.0.0.1:5000")
    print(f"From other computers:  https://{local_ip}:5000")
    print("(other computers must be on the same Wi-Fi/network)")
    print()
    print("NOTE: Browsers will show a security warning because this")
    print("uses a self-signed certificate, not a certificate from a")
    print("trusted authority. This is expected. Click 'Advanced' then")
    print("'Proceed' to continue. Camera/microphone access requires")
    print("HTTPS on any address other than 127.0.0.1/localhost, which")
    print("is why this app now runs on https:// instead of http://.")
    print("=" * 60)

    app.run(
        host="0.0.0.0",
        port=5000,
        debug=False,
        use_reloader=False,
        ssl_context="adhoc"
    )
