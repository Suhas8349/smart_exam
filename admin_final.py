from flask import Flask, render_template, request, redirect, url_for, session, flash, jsonify, send_file, send_from_directory
from openpyxl import Workbook, load_workbook
from werkzeug.security import generate_password_hash, check_password_hash
from functools import wraps
import os
from zipfile import BadZipFile

# Gemini API key for AI question generation.
# Configure GEMINI_API_KEY in the environment; never hard-code a secret.
import uuid
import json
import re
import time
import traceback
import hmac
import requests
from datetime import datetime

# ============================================================
# REMOTE ADMIN -> STUDENT LIVE VOICE BROADCAST
# ============================================================
# admin_app.py proxies WebRTC signaling to student_app.py.  The
# browser-to-browser audio itself uses WebRTC; the Flask endpoints
# only exchange offer/answer messages.
STUDENT_SIGNAL_BASE_URL = os.environ.get(
    "STUDENT_SIGNAL_BASE_URL", "https://127.0.0.1:5000"
).rstrip("/")
VOICE_SIGNAL_TOKEN = os.environ.get(
    "VOICE_SIGNAL_TOKEN", "CHANGE_THIS_SHARED_VOICE_TOKEN"
)
STUDENT_SIGNAL_VERIFY_SSL = os.environ.get(
    "STUDENT_SIGNAL_VERIFY_SSL", "false"
).strip().lower() in ("1", "true", "yes", "on")


app = Flask(__name__)

app.secret_key = "admin_teacher_management_system_secret_key"

# Anchor every shared path to THIS FILE's own folder — must match
# the same fix in student_app.py exactly, since both apps need to
# agree on the physical location of these folders/file.
BASE_DIR = os.path.dirname(os.path.abspath(__file__))

AI_BUILD = "GEMINI-ONLY-2026-09-02"
print(f"[STARTUP] {AI_BUILD} | AI provider: Google Gemini | model: gemini-3.1-flash-lite")

DATABASE = os.path.join(BASE_DIR, "database.xlsx")
RECORDINGS_FOLDER = os.path.join(BASE_DIR, "recordings")
LIVE_FRAMES_FOLDER = os.path.join(BASE_DIR, "live_frames")
RECORDING_PARTS_FOLDER = os.path.join(RECORDINGS_FOLDER, ".examguard_admin_parts")
os.makedirs(RECORDING_PARTS_FOLDER, exist_ok=True)

# FIX: this used to be the bare string "downloads", which Flask
# resolves relative to the process's CURRENT WORKING DIRECTORY, not
# this file's folder. If the app is ever launched from a different
# working directory (a scheduler, a service manager, a shortcut,
# running it from a parent folder, etc.) that relative folder may not
# exist or may not be writable, and download_workbook.save(filepath)
# throws an unhandled exception -> Flask shows a raw 500 error page,
# which is exactly the "results/download show error" symptom. Anchor
# it to BASE_DIR like every other shared folder so it always resolves
# to the same place regardless of how/where the app is started.
DOWNLOADS_FOLDER = os.path.join(BASE_DIR, "downloads")

# STUDENT -> ADMIN RESULT / RECORDING SYNC
RECORDING_SYNC_TOKEN = os.environ.get("EXAMGUARD_RECORDING_SYNC_TOKEN", "EXAMGUARD-RECORDING-2026-LOCAL").strip()
LIVE_MONITOR_BUILD = "V3-DIRECT-PULL"
LIVE_SYNC_TOKEN = os.environ.get("EXAMGUARD_LIVE_SYNC_TOKEN", "EXAMGUARD-LIVE-2026-LOCAL").strip()



# ============================================================
# ============================================================
# ============================================================
# DATABASE FILE-SAFETY LAYER
# ============================================================
# Excel .xlsx files are ZIP archives. Both Flask apps access the same
# database.xlsx. Use an atomic lock-file protocol that does not require
# Windows named-mutex permissions, and use atomic temporary-file replacement
# for writes. This avoids exposing a half-written XLSX to the other app.

from zipfile import BadZipFile, ZipFile
import shutil
import tempfile
import os
import time

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
                # O_EXCL makes creation atomic across processes on Windows.
                self.fd = os.open(
                    self.path,
                    os.O_CREAT | os.O_EXCL | os.O_WRONLY,
                )
                payload = f"pid={os.getpid()}\ntime={time.time()}\n"
                os.write(self.fd, payload.encode("utf-8", "replace"))
                return
            except FileExistsError:
                try:
                    age = time.time() - os.path.getmtime(self.path)
                    if age > LOCK_STALE_SECONDS:
                        os.remove(self.path)
                        continue
                except (FileNotFoundError, OSError):
                    pass
                if time.monotonic() >= deadline:
                    raise TimeoutError("Timed out waiting for ExamGuard database lock")
                time.sleep(0.05)
            except OSError as exc:
                raise OSError(f"Could not create ExamGuard database lock: {exc}") from exc

    def release(self):
        if self.fd is not None:
            try:
                os.close(self.fd)
            finally:
                self.fd = None
        try:
            os.remove(self.path)
        except FileNotFoundError:
            pass
        except OSError:
            pass


def _database_lock(timeout=30.0):
    lock = _FileLock(DATABASE_LOCK)
    lock.acquire(timeout)
    return lock


def _database_unlock(lock_obj):
    lock_obj.release()


def _restore_backup_locked():
    if not _valid_xlsx(DATABASE_BACKUP):
        return False
    temp_path = None
    try:
        fd, temp_path = tempfile.mkstemp(
            prefix="database_restore_", suffix=".xlsx", dir=BASE_DIR
        )
        os.close(fd)
        shutil.copy2(DATABASE_BACKUP, temp_path)
        if not _valid_xlsx(temp_path):
            return False
        os.replace(temp_path, DATABASE)
        temp_path = None
        print("[DATABASE] Restored database.xlsx from last-known-good backup.")
        return True
    except OSError as exc:
        print(f"[DATABASE] Backup restore failed: {exc}")
        return False
    finally:
        if temp_path and os.path.exists(temp_path):
            try:
                os.remove(temp_path)
            except OSError:
                pass


def load_database(*args, **kwargs):
    last_error = None

    for attempt in range(10):
        try:
            if _valid_xlsx(DATABASE):
                try:
                    return load_workbook(DATABASE, *args, **kwargs)
                except (BadZipFile, EOFError, OSError) as exc:
                    last_error = exc
            else:
                last_error = BadZipFile(
                    "database.xlsx is not a valid XLSX archive"
                )

        except OSError as exc:
            last_error = exc

        time.sleep(0.20 + 0.10 * attempt)

    raise last_error

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
    last_error = None
    for attempt in range(10):
        try:
            if _valid_xlsx(DATABASE):
                return load_workbook(DATABASE, *args, **kwargs)
            last_error = BadZipFile("database.xlsx is not a valid XLSX archive")
        except (BadZipFile, EOFError, OSError) as exc:
            last_error = exc
        time.sleep(0.20 + 0.10 * attempt)
    # One recovery attempt from the last-known-good backup.
    if _valid_xlsx(DATABASE_BACKUP):
        shutil.copy2(DATABASE_BACKUP, DATABASE)
        return load_workbook(DATABASE, *args, **kwargs)
    raise last_error


def save_database(workbook):
    lock = _FileLock(DATABASE_LOCK)
    temp_path = None
    try:
        lock.acquire(30.0)
        if _valid_xlsx(DATABASE):
            try:
                shutil.copy2(DATABASE, DATABASE_BACKUP)
            except OSError as exc:
                print("[DATABASE] Backup warning:", exc)
        fd, temp_path = tempfile.mkstemp(prefix="database_write_", suffix=".xlsx", dir=BASE_DIR)
        os.close(fd)
        workbook.save(temp_path)
        if not _valid_xlsx(temp_path):
            raise BadZipFile("Temporary database write failed validation")
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

FIXED_SUBJECTS = [
    'Default (Manual Questions)',
    'Maths / Mathematics',
    'Physics',
    'Chemistry',
    'Biology',
    'History',
    'Geography',
    'Political Science',
    'English',
    'Computer Fundamentals',
    'General Knowledge',
    'Python',
    'Java',
    'C Programming',
    'C++',
    'Machine Learning',
    'Artificial Intelligence',
    'Data Science',
    'Database Management Systems',
    'Web Development',
    'Operating Systems',
    'Computer Networks',
    'Cybersecurity',
    'Electronics & Digital Logic',
    'Indian Constitution',
    'Indian Polity',
    'Indian History',
    'Indian Epics (Ramayana, Mahabharata & Puranic Stories)',
    'Astrophysics',
    'Astronomy',
    'Geology',
    'Environmental Science',
    'Statistics',
    'Logical Reasoning',
    'Current Affairs',
    'Sports',
    'Economics',
    'Psychology',
    'Sociology',
    'World History',
    'World Cultures',
    'Financial Literacy',
    'Marketing',
    'Communication Skills',
    'Discrete Mathematics',
]

AI_SUBJECTS = set(FIXED_SUBJECTS[1:])
MANUAL_SUBJECT = FIXED_SUBJECTS[0]

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
            "Correct Answer",
            "Available From",
            "Available Until",
            "Duration Minutes"
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

    workbook.close()


def ensure_result_student_detail_columns():
    """Add 'Student Email' and 'Submitted At' to Results, if missing.

    These let the recordings page show who took the exam, their email,
    and when they submitted, alongside each recording — without
    disturbing any existing column positions or data.
    """
    workbook = load_database()

    if "Results" not in workbook.sheetnames:
        workbook.close()
        return

    sheet = workbook["Results"]
    headers = [cell.value for cell in sheet[1]]
    changed = False

    if "Student Email" not in headers:
        sheet.cell(row=1, column=sheet.max_column + 1, value="Student Email")
        changed = True

    headers = [cell.value for cell in sheet[1]]

    if "Submitted At" not in headers:
        sheet.cell(row=1, column=sheet.max_column + 1, value="Submitted At")
        changed = True

    if changed:
        save_database(workbook)

    workbook.close()


# ============================================================
# EXAM AVAILABILITY WINDOW SUPPORT (optional start/end time)
# ============================================================

def ensure_exam_timing_columns():

    workbook = load_database()

    if "Exams" not in workbook.sheetnames:
        workbook.close()
        return

    sheet = workbook["Exams"]

    headers = [cell.value for cell in sheet[1]]

    changed = False

    if "Available From" not in headers:
        sheet.cell(row=1, column=sheet.max_column + 1, value="Available From")
        changed = True

    headers = [cell.value for cell in sheet[1]]

    if "Available Until" not in headers:
        sheet.cell(row=1, column=sheet.max_column + 1, value="Available Until")
        changed = True

    if changed:
        save_database(workbook)

    workbook.close()


def ensure_exam_duration_column():
    """Add a per-exam duration column without changing existing column positions."""
    workbook = load_database()
    if "Exams" not in workbook.sheetnames:
        workbook.close()
        return

    sheet = workbook["Exams"]
    headers = [cell.value for cell in sheet[1]]
    changed = False

    if "Duration Minutes" not in headers:
        sheet.cell(row=1, column=sheet.max_column + 1, value="Duration Minutes")
        changed = True
        duration_col = sheet.max_column
        # Existing exams did not have a timer. Give them a safe default.
        for row in range(2, sheet.max_row + 1):
            if not sheet.cell(row=row, column=duration_col).value:
                sheet.cell(row=row, column=duration_col, value=30)

    if changed:
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




def teacher_login_required(function):

    @wraps(function)
    def wrapper(*args, **kwargs):

        if "teacher_id" not in session:

            return redirect(url_for("login"))

        return function(*args, **kwargs)

    return wrapper


def safe_results_route(redirect_endpoint):
    """
    Wraps a results/download view so that ANY unexpected error (a
    missing sheet, a bad row, a disk/permission problem while saving
    the .xlsx, etc.) is caught, logged to the console with a full
    traceback for debugging, and turned into a friendly flash message
    instead of Flask's raw 500 error page. This is what the results
    and download buttons were doing before — failing silently with a
    blank/generic error and no way to tell what actually went wrong.
    """
    def decorator(function):

        @wraps(function)
        def wrapper(*args, **kwargs):

            try:
                return function(*args, **kwargs)

            except Exception as e:

                print(
                    f"[{function.__name__}] ERROR:",
                    str(e)
                )
                traceback.print_exc()

                flash(
                    "Something went wrong loading/downloading these "
                    f"results ({str(e)}). Please try again, and if it "
                    "keeps happening, check the server console for the "
                    "full error.",
                    "error"
                )

                return redirect(url_for(redirect_endpoint))

        return wrapper

    return decorator


# ============================================================
# STUDENT LOGIN REQUIRED
# ============================================================




# ============================================================
# HOME — landing page for the admin/teacher management system.
# There is no student registration/login anywhere in this app.
# ============================================================

@app.route("/")
def index():

    html = """
    <!doctype html>
    <html>
    <head>
      <title>Exam Management System</title>
    </head>
    <body>
      <div style="max-width:640px;margin:80px auto;padding:0 20px;font-family:'Segoe UI',Arial,sans-serif;">
        <div style="font:600 11.5px monospace;letter-spacing:.08em;text-transform:uppercase;color:#9d85ff;margin-bottom:10px;">
          Management System
        </div>
        <h1 style="font-size:32px;margin:0 0 10px;color:#f1f0f7;background:linear-gradient(120deg,#f1f0f7 40%,#9d85ff);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent;">Exam Management System</h1>
        <p style="color:#b7b3cc;font-size:15px;margin-bottom:36px;">
          This system is separate from the student exam portal. Only teachers and
          administrators can access this system.
        </p>

        <div style="display:grid;grid-template-columns:1fr 1fr;gap:18px;">
          <div class="ai-role-card" style="background:rgba(20,24,42,0.62);border:1px solid rgba(157,133,255,0.28);border-radius:14px;padding:24px;box-shadow:0 10px 30px rgba(0,0,0,0.35);backdrop-filter:blur(12px);transition:transform .25s ease, box-shadow .25s ease;">
            <div style="font:600 11px monospace;letter-spacing:.06em;text-transform:uppercase;color:#9d85ff;margin-bottom:8px;">Instructor</div>
            <h2 style="font-size:18px;margin:0 0 8px;color:#f1f0f7;">Teacher</h2>
            <p style="color:#b7b3cc;font-size:13.5px;margin-bottom:18px;">Create exams and review student results.</p>
            <a href="/login" style="margin-right:14px;color:#9d85ff;font-weight:600;">Login</a>
            <a href="/register" style="color:#9d85ff;font-weight:600;">Register</a>
          </div>

          <div class="ai-role-card" style="background:rgba(20,24,42,0.62);border:1px solid rgba(157,133,255,0.28);border-radius:14px;padding:24px;box-shadow:0 10px 30px rgba(0,0,0,0.35);backdrop-filter:blur(12px);transition:transform .25s ease, box-shadow .25s ease;">
            <div style="font:600 11px monospace;letter-spacing:.06em;text-transform:uppercase;color:#9d85ff;margin-bottom:8px;">Oversight</div>
            <h2 style="font-size:18px;margin:0 0 8px;color:#f1f0f7;">Admin</h2>
            <p style="color:#b7b3cc;font-size:13.5px;margin-bottom:18px;">Monitor exams live and review recordings.</p>
            <a href="/admin/login" style="margin-right:14px;color:#9d85ff;font-weight:600;">Login</a>
            <a href="/admin/register" style="color:#9d85ff;font-weight:600;">Register</a>
          </div>
        </div>
      </div>
      <style>.ai-role-card:hover{transform:translateY(-5px) !important;box-shadow:0 18px 42px rgba(0,0,0,0.45) !important;}</style>
    </body>
    </html>
    """

    return html


# ============================================================
# ======================= TEACHER =============================
# ============================================================




@app.route("/register", methods=["GET", "POST"])
def register():

    if request.method == "POST":

        teacher_id = request.form["teacher_id"].strip()
        teacher_name = request.form["teacher_name"].strip()
        email = request.form["email"].strip()
        password = request.form["password"]

        if not teacher_id or not teacher_name or not email or not password:

            flash("All fields are required.", "error")

            return redirect(url_for("register"))

        workbook = load_database()

        sheet = workbook["Teachers"]

        for row in sheet.iter_rows(min_row=2, values_only=True):

            if row[0] == teacher_id:

                workbook.close()

                flash("Teacher ID already exists.", "error")

                return redirect(url_for("register"))

            if row[2] == email:

                workbook.close()

                flash("Email already registered.", "error")

                return redirect(url_for("register"))

        hashed_password = generate_password_hash(password)

        sheet.append([
            teacher_id,
            teacher_name,
            email,
            hashed_password
        ])

        save_database(workbook)

        workbook.close()

        flash(
            "Teacher registration successful. Please login.",
            "success"
        )

        return redirect(url_for("login"))

    return render_template("register.html")


# ============================================================
# TEACHER LOGIN
# ============================================================



@app.route("/login", methods=["GET", "POST"])
def login():

    if request.method == "POST":

        teacher_id = request.form["teacher_id"].strip()
        password = request.form["password"]

        workbook = load_database()

        sheet = workbook["Teachers"]

        for row in sheet.iter_rows(min_row=2, values_only=True):

            if row[0] == teacher_id:

                if check_password_hash(row[3], password):

                    session["teacher_id"] = row[0]
                    session["teacher_name"] = row[1]
                    session["teacher_email"] = row[2]

                    workbook.close()

                    return redirect(url_for("dashboard"))

                else:

                    workbook.close()

                    flash(
                        "Incorrect password.",
                        "error"
                    )

                    return redirect(url_for("login"))

        workbook.close()

        flash(
            "Teacher ID not found.",
            "error"
        )

        return redirect(url_for("login"))

    return render_template("login.html")


# ============================================================
# TEACHER DASHBOARD
# ============================================================



@app.route("/dashboard")
@teacher_login_required
def dashboard():

    teacher_id = session["teacher_id"]

    workbook = load_database()

    sheet = workbook["Exams"]

    exams = {}

    for row in sheet.iter_rows(min_row=2, values_only=True):

        exam_id = row[0]

        if row[1] == teacher_id:

            if exam_id not in exams:

                exams[exam_id] = {
                    "exam_id": exam_id,
                    "subject_name": row[3],
                    "subject_code": row[4],
                    "teacher_name": row[2],
                    "question_count": 0
                }

            exams[exam_id]["question_count"] += 1

    workbook.close()

    exam_list = list(exams.values())

    exam_list.reverse()

    return render_template(
        "dashboard.html",
        exams=exam_list
    )


# ============================================================
# CREATE EXAM
# ============================================================



@app.route("/create_exam", methods=["GET", "POST"])
@teacher_login_required
def create_exam():

    if request.method == "POST":

        subject_name = request.form["subject_name"].strip()
        subject_code = request.form["subject_code"].strip()

        # =====================================================
        # OPTIONAL EXAM AVAILABILITY WINDOW
        # Both fields are optional. If left blank, the exam has
        # no time restriction (available any time), same as before.
        # =====================================================

        def parse_datetime_local(raw_value):
            """
            HTML <input type="datetime-local"> is supposed to submit
            'YYYY-MM-DDTHH:MM', but some browsers/OS locale settings
            submit 'YYYY-MM-DDTHH:MM:SS' with seconds included, which
            a strict single-format parser rejects as "invalid" even
            though the date/time itself is completely valid. Try
            both formats before giving up.
            """
            raw_value = raw_value.strip()
            for fmt in ("%Y-%m-%dT%H:%M:%S", "%Y-%m-%dT%H:%M"):
                try:
                    return datetime.strptime(raw_value, fmt)
                except ValueError:
                    continue
            return None

        available_from_raw = request.form.get("available_from", "").strip()
        available_until_raw = request.form.get("available_until", "").strip()

        available_from = ""
        available_until = ""

        if available_from_raw:
            dt = parse_datetime_local(available_from_raw)
            if dt is None:
                flash("Invalid 'available from' date/time.", "error")
                return redirect(url_for("create_exam"))
            available_from = dt.strftime("%Y-%m-%d %H:%M")

        if available_until_raw:
            dt = parse_datetime_local(available_until_raw)
            if dt is None:
                flash("Invalid 'available until' date/time.", "error")
                return redirect(url_for("create_exam"))
            available_until = dt.strftime("%Y-%m-%d %H:%M")

        if available_from and available_until:
            if datetime.strptime(available_until, "%Y-%m-%d %H:%M") <= datetime.strptime(available_from, "%Y-%m-%d %H:%M"):
                flash("'Available until' must be after 'available from'.", "error")
                return redirect(url_for("create_exam"))

        # Duration is synchronized with the availability window. When both
        # From and Until are supplied, the authoritative duration is the
        # exact minute difference between them. The browser UI also keeps
        # the three fields synchronized live.
        if available_from and available_until:
            start_dt = datetime.strptime(available_from, "%Y-%m-%d %H:%M")
            end_dt = datetime.strptime(available_until, "%Y-%m-%d %H:%M")
            duration_minutes = int((end_dt - start_dt).total_seconds() // 60)
        else:
            try:
                duration_minutes = int(request.form.get("duration_minutes", "30"))
            except ValueError:
                duration_minutes = 0

        if duration_minutes < 1 or duration_minutes > 480:
            flash("Exam duration must be between 1 and 480 minutes.", "error")
            return redirect(url_for("create_exam"))

        if not subject_name or not subject_code:

            flash(
                "Subject name and subject code are required.",
                "error"
            )

            return redirect(url_for("create_exam"))

        if subject_name not in FIXED_SUBJECTS:
            flash(
                "Please select one of the fixed subjects from the dropdown.",
                "error"
            )
            return redirect(url_for("create_exam"))

        # =====================================================
        # NUMBER OF QUESTIONS (teacher-specified, not fixed at 20)
        # =====================================================
        try:
            num_questions = int(request.form.get("num_questions", "0"))
        except ValueError:
            num_questions = 0

        if num_questions < 1 or num_questions > 100:
            flash(
                "Number of questions must be between 1 and 100.",
                "error"
            )
            return redirect(url_for("create_exam"))

        questions = []

        for i in range(1, num_questions + 1):

            question = request.form.get(
                f"question_{i}", ""
            ).strip()

            option_a = request.form.get(
                f"option_a_{i}", ""
            ).strip()

            option_b = request.form.get(
                f"option_b_{i}", ""
            ).strip()

            option_c = request.form.get(
                f"option_c_{i}", ""
            ).strip()

            option_d = request.form.get(
                f"option_d_{i}", ""
            ).strip()

            correct_answer = request.form.get(
                f"correct_{i}", ""
            ).strip()

            if not question:

                flash(
                    f"Question {i} is empty.",
                    "error"
                )

                return redirect(url_for("create_exam"))

            if not option_a or not option_b or not option_c or not option_d:

                flash(
                    f"All options are required for Question {i}.",
                    "error"
                )

                return redirect(url_for("create_exam"))

            if correct_answer not in ["A", "B", "C", "D"]:

                flash(
                    f"Select correct answer for Question {i}.",
                    "error"
                )

                return redirect(url_for("create_exam"))

            questions.append({
                "question": question,
                "option_a": option_a,
                "option_b": option_b,
                "option_c": option_c,
                "option_d": option_d,
                "correct_answer": correct_answer
            })

        exam_id = "EXAM-" + uuid.uuid4().hex[:8].upper()

        teacher_id = session["teacher_id"]
        teacher_name = session["teacher_name"]

        workbook = load_database()

        sheet = workbook["Exams"]

        for number, q in enumerate(questions, start=1):

            sheet.append([
                exam_id,
                teacher_id,
                teacher_name,
                subject_name,
                subject_code,
                number,
                q["question"],
                q["option_a"],
                q["option_b"],
                q["option_c"],
                q["option_d"],
                q["correct_answer"],
                available_from,
                available_until,
                duration_minutes
            ])

        save_database(workbook)

        workbook.close()

        flash(
            f"Exam created successfully. Exam ID: {exam_id}",
            "success"
        )

        return redirect(url_for("dashboard"))

    # =========================================================
    # GET — also hand the template the list of subjects already
    # used in past exams, so a teacher creating a new exam can pick
    # one from a scrollable list instead of re-typing the exact same
    # name/code every time (and risking a typo that splits it into a
    # second "different" subject in the admin/results views).
    # =========================================================
    existing_subjects = []
    seen_codes = set()

    workbook = load_database()
    exam_sheet = workbook["Exams"]

    for row in exam_sheet.iter_rows(min_row=2, values_only=True):
        code = row[4]
        if code and code not in seen_codes:
            seen_codes.add(code)
            existing_subjects.append({
                "subject_name": row[3],
                "subject_code": code
            })

    workbook.close()

    existing_subjects.sort(key=lambda s: (s["subject_name"] or "").lower())

    return render_template(
        "create_exam.html",
        existing_subjects=existing_subjects,
        fixed_subjects=FIXED_SUBJECTS,
        ai_subjects=AI_SUBJECTS,
    )


@app.route("/teacher/exams/manage")
@teacher_login_required
def manage_exams():
    teacher_id = session["teacher_id"]
    workbook = load_database()
    sheet = workbook["Exams"]
    exams = {}
    for row in sheet.iter_rows(min_row=2, values_only=True):
        if row[1] == teacher_id:
            exams.setdefault(row[0], {
                "exam_id": row[0], "subject_name": row[3],
                "subject_code": row[4], "question_count": 0,
                "duration_minutes": row[14] if len(row) > 14 and row[14] else 30,
            })
            exams[row[0]]["question_count"] += 1
    workbook.close()
    return render_template("manage_exams.html", exams=list(exams.values()))


# ============================================================
# EDIT / MANAGE AN ALREADY-CREATED EXAM
# ============================================================

@app.route("/teacher/exam/<exam_id>/delete", methods=["POST"])
@teacher_login_required
def delete_exam(exam_id):
    """Delete one teacher-owned exam and its question rows.

    Exams with recorded student results are intentionally protected so deleting
    the question set cannot silently destroy or invalidate historical results.
    """
    teacher_id = session["teacher_id"]
    workbook = load_database()
    exam_sheet = workbook["Exams"]

    row_numbers = []
    for excel_row, row in enumerate(exam_sheet.iter_rows(min_row=2, values_only=True), start=2):
        if row[0] == exam_id and row[1] == teacher_id:
            row_numbers.append(excel_row)

    if not row_numbers:
        workbook.close()
        flash("Exam not found or you are not authorized to remove it.", "error")
        return redirect(url_for("manage_exams"))

    if "Results" in workbook.sheetnames:
        results_sheet = workbook["Results"]
        has_results = any(
            r[3] == exam_id
            for r in results_sheet.iter_rows(min_row=2, values_only=True)
            if len(r) > 3
        )
        if has_results:
            workbook.close()
            flash("This exam has student results, so it cannot be removed.", "error")
            return redirect(url_for("manage_exams"))

    for excel_row in reversed(row_numbers):
        exam_sheet.delete_rows(excel_row, 1)

    save_database(workbook)
    workbook.close()
    flash(f"Exam {exam_id} removed successfully.", "success")
    return redirect(url_for("manage_exams"))


@app.route("/teacher/exam/<exam_id>/edit", methods=["GET", "POST"])
@teacher_login_required
def edit_exam(exam_id):
    teacher_id = session["teacher_id"]
    workbook = load_database()
    exam_sheet = workbook["Exams"]

    rows = []
    row_numbers = []
    for excel_row, row in enumerate(exam_sheet.iter_rows(min_row=2, values_only=True), start=2):
        if row[0] == exam_id and row[1] == teacher_id:
            row_numbers.append(excel_row)
            rows.append(row)

    if not rows:
        workbook.close()
        flash("Exam not found or you are not authorized to edit it.", "error")
        return redirect(url_for("dashboard"))

    # Once a student has a recorded result, changing the question set would
    # make that historical result ambiguous, so keep completed exams locked.
    if request.method == "POST":
        if "Results" in workbook.sheetnames:
            results_sheet = workbook["Results"]
            has_results = any(
                r[3] == exam_id
                for r in results_sheet.iter_rows(min_row=2, values_only=True)
                if len(r) > 3
            )
            if has_results:
                workbook.close()
                flash("This exam already has student results, so its questions cannot be changed.", "error")
                return redirect(url_for("dashboard"))

        try:
            duration_minutes = int(request.form.get("duration_minutes", "30"))
            num_questions = int(request.form.get("num_questions", "0"))
        except ValueError:
            duration_minutes = 0
            num_questions = 0

        if duration_minutes < 1 or duration_minutes > 480:
            workbook.close()
            flash("Exam duration must be between 1 and 480 minutes.", "error")
            return redirect(url_for("edit_exam", exam_id=exam_id))
        if num_questions < 1 or num_questions > 100:
            workbook.close()
            flash("Number of questions must be between 1 and 100.", "error")
            return redirect(url_for("edit_exam", exam_id=exam_id))

        questions = []
        for i in range(1, num_questions + 1):
            q = request.form.get(f"question_{i}", "").strip()
            a = request.form.get(f"option_a_{i}", "").strip()
            b = request.form.get(f"option_b_{i}", "").strip()
            c = request.form.get(f"option_c_{i}", "").strip()
            d = request.form.get(f"option_d_{i}", "").strip()
            correct = request.form.get(f"correct_{i}", "").strip()
            if not q or not a or not b or not c or not d or correct not in ["A", "B", "C", "D"]:
                workbook.close()
                flash(f"Please complete Question {i} and select its correct answer.", "error")
                return redirect(url_for("edit_exam", exam_id=exam_id))
            questions.append((q, a, b, c, d, correct))

        subject_name = rows[0][3]
        subject_code = rows[0][4]
        teacher_name = rows[0][2]
        available_from = rows[0][12] if len(rows[0]) > 12 else ""
        available_until = rows[0][13] if len(rows[0]) > 13 else ""

        # Delete this exam's old question rows, then write the revised set.
        for excel_row in reversed(row_numbers):
            exam_sheet.delete_rows(excel_row, 1)

        for number, (q, a, b, c, d, correct) in enumerate(questions, start=1):
            exam_sheet.append([
                exam_id, teacher_id, teacher_name, subject_name, subject_code,
                number, q, a, b, c, d, correct,
                available_from, available_until, duration_minutes
            ])

        save_database(workbook)
        workbook.close()
        flash(f"Exam {exam_id} updated successfully.", "success")
        return redirect(url_for("dashboard"))

    # GET
    duration = rows[0][14] if len(rows[0]) > 14 and rows[0][14] else 30
    try:
        duration = int(duration)
    except (TypeError, ValueError):
        duration = 30

    questions = []
    for row in rows:
        questions.append({
            "number": row[5], "question": row[6],
            "option_a": row[7], "option_b": row[8],
            "option_c": row[9], "option_d": row[10],
            "correct_answer": row[11]
        })
    workbook.close()

    return render_template(
        "edit_exam.html",
        exam_id=exam_id,
        subject_name=rows[0][3],
        subject_code=rows[0][4],
        duration_minutes=duration,
        questions=questions,
    )


@app.route("/create_exam/ai_status", methods=["GET"])
def ai_status():
    key = os.environ.get("GEMINI_API_KEY", "").strip()
    return jsonify({
        "ai_provider": "Google Gemini",
        "model": "gemini-3.1-flash-lite",
        "configured": bool(key and key != "PASTE_YOUR_GEMINI_API_KEY_HERE"),
        "build": AI_BUILD,
    })

@app.route("/create_exam/ai_generate_questions", methods=["POST"])
@teacher_login_required
def ai_generate_questions():
    """Generate editable MCQs with Google Gemini. Nothing is saved here."""
    try:
        payload = request.get_json(silent=True) or {}
        subject_name = str(payload.get("subject_name", "")).strip()

        if subject_name == MANUAL_SUBJECT:
            return jsonify({
                "success": False,
                "error": "Default (Manual Questions) is manual-only. Use Add Blank Questions instead."
            }), 400

        if subject_name not in AI_SUBJECTS:
            return jsonify({
                "success": False,
                "error": "Please select one of the supported AI subjects."
            }), 400
        num_questions = int(payload.get("num_questions", 0) or 0)
        difficulty = str(payload.get("difficulty", "medium")).strip().lower() or "medium"
        notes = str(payload.get("notes", "")).strip()

        if not subject_name:
            return jsonify({"success": False, "error": "Select a subject first."}), 400

        if num_questions < 1 or num_questions > 100:
            return jsonify({"success": False, "error": "Number of questions must be between 1 and 100."}), 400

        if difficulty not in ("easy", "medium", "hard"):
            return jsonify({"success": False, "error": "Difficulty must be Easy, Medium, or Hard."}), 400

        api_key = os.environ.get("GEMINI_API_KEY", "").strip()
        if not api_key or api_key == "PASTE_YOUR_GEMINI_API_KEY_HERE":
            return jsonify({
                "success": False,
                "error": "Gemini is not configured yet. Set GEMINI_API_KEY in the environment used by this Flask process, then restart Flask/Spyder."
            }), 400

        prompt = (
            f"Generate exactly {num_questions} multiple-choice exam questions on the subject "
            f"{subject_name}. Difficulty: {difficulty}. "
            "Each question must have exactly 4 plausible options and exactly one correct option. "
            "Return ONLY a JSON array. Every item must contain exactly these fields: "
            "question, option_a, option_b, option_c, option_d, correct_answer. "
            "correct_answer must be exactly one of A, B, C, or D and must match the correct option. "
            "Do not include markdown, explanations, numbering outside the JSON, or extra fields. "
        )
        if notes:
            prompt += f"Teacher's additional instructions: {notes}."

        # Gemini 3.1 Flash-Lite is the configured GA model.
        model = "gemini-3.1-flash-lite"
        url = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
        response = requests.post(
            url,
            headers={
                "x-goog-api-key": api_key,
                "Content-Type": "application/json"
            },
            json={
                "contents": [{
                    "parts": [{"text": prompt}]
                }],
                "generationConfig": {
                    "responseMimeType": "application/json",
                    "temperature": 0.8,
                    "maxOutputTokens": min(max(4096, num_questions * 220), 32768)
                }
            },
            timeout=120
        )

        try:
            response_data = response.json()
        except ValueError:
            response_data = {}

        if not response.ok:
            err = response_data.get("error", {}) if isinstance(response_data, dict) else {}
            message = err.get("message") or response.text or "Unknown Gemini API error."
            if response.status_code in (401, 403):
                message = (
                    f"Gemini authentication/permission error ({response.status_code}). "
                    "Make sure the Gemini API key belongs to the same Google AI Studio project, "
                    "the key is active, and the key is loaded by THIS Flask process. Details: " + message
                )
            return jsonify({
                "success": False,
                "error": f"Gemini API error ({response.status_code}): {message}"
            }), 502

        candidates = response_data.get("candidates", [])
        if not candidates:
            return jsonify({"success": False, "error": "Gemini returned no candidates."}), 502

        parts = candidates[0].get("content", {}).get("parts", [])
        raw_text = "".join(
            str(part.get("text", ""))
            for part in parts
            if isinstance(part, dict)
        ).strip()

        if not raw_text:
            finish_reason = candidates[0].get("finishReason", "unknown")
            return jsonify({
                "success": False,
                "error": f"Gemini returned an empty response (finish reason: {finish_reason})."
            }), 502

        # Be tolerant if a model still wraps the JSON in a code fence.
        if raw_text.startswith("```"):
            lines = raw_text.splitlines()
            if lines and lines[0].strip().startswith("```"):
                lines = lines[1:]
            if lines and lines[-1].strip() == "```":
                lines = lines[:-1]
            raw_text = "\n".join(lines).strip()

        try:
            questions = json.loads(raw_text)
        except json.JSONDecodeError:
            # Try extracting the outermost JSON array if there is stray text.
            first = raw_text.find("[")
            last = raw_text.rfind("]")
            if first == -1 or last <= first:
                raise ValueError("Gemini did not return valid JSON.")
            questions = json.loads(raw_text[first:last + 1])

        if not isinstance(questions, list):
            raise ValueError("Gemini response was not a JSON array.")

        cleaned = []
        required = ("question", "option_a", "option_b", "option_c", "option_d", "correct_answer")
        for q in questions:
            if not isinstance(q, dict):
                continue
            correct = str(q.get("correct_answer", "")).strip().upper()
            values = {key: str(q.get(key, "")).strip() for key in required}
            if correct not in ("A", "B", "C", "D"):
                continue
            if any(not values[key] for key in required[:-1]):
                continue
            values["correct_answer"] = correct
            cleaned.append(values)
            if len(cleaned) >= num_questions:
                break

        if len(cleaned) != num_questions:
            raise ValueError(
                f"Gemini returned {len(cleaned)} valid questions, but {num_questions} were requested. Please try again."
            )

        return jsonify({"success": True, "questions": cleaned})

    except requests.Timeout:
        return jsonify({
            "success": False,
            "error": "Gemini request timed out. Please try again with fewer questions."
        }), 504
    except requests.RequestException as e:
        print("[ai_generate_questions] NETWORK ERROR:", str(e))
        return jsonify({
            "success": False,
            "error": f"Could not connect to Gemini: {str(e)}"
        }), 502
    except Exception as e:
        print("[ai_generate_questions] ERROR:", str(e))
        traceback.print_exc()
        return jsonify({
            "success": False,
            "error": f"AI question generation failed: {str(e)}"
        }), 500


# ============================================================
# ======================= STUDENT =============================
# ============================================================


# ============================================================
# STUDENT REGISTER
# ============================================================





# ====================== STUDENT -> ADMIN SYNC ======================
def _sync_token_valid(value):
    expected=RECORDING_SYNC_TOKEN
    return bool(expected and expected != "CHANGE_THIS_SHARED_RECORDING_SYNC_TOKEN" and value) and hmac.compare_digest(str(value), expected)

def _safe_sync_filename(value):
    name=os.path.basename(str(value or "").strip()); name=re.sub(r"[^A-Za-z0-9._-]+","_",name)
    if not name.lower().endswith(".webm"): name += ".webm"
    return name[:220] or "recording.webm"

def _ensure_admin_sync_schema(wb):
    req=["Result ID","Student ID","Student Name","Student Email","Exam ID","Subject Name","Subject Code","Total Questions","Correct Answers","Wrong Answers","Score","Percentage","Recording File","Exam Status","Unattempted Answers","Submitted At"]
    ws=wb["Results"] if "Results" in wb.sheetnames else wb.create_sheet("Results"); hs=[c.value for c in ws[1]] if ws.max_row else []
    if not hs:
        for i,h in enumerate(req,1): ws.cell(1,i,h)
    else:
        for h in req:
            if h not in hs: ws.cell(1,ws.max_column+1,h); hs.append(h)
    det=["Result ID","Student ID","Student Name","Exam ID","Subject Name","Subject Code","Question Number","Question","Student Answer","Correct Answer","Status"]
    ds=wb["ResultDetails"] if "ResultDetails" in wb.sheetnames else wb.create_sheet("ResultDetails"); hd=[c.value for c in ds[1]] if ds.max_row else []
    if not hd:
        for i,h in enumerate(det,1): ds.cell(1,i,h)
    else:
        for h in det:
            if h not in hd: ds.cell(1,ds.max_column+1,h); hd.append(h)
    return ws,ds

def _upsert_admin_sync_result(wb,p):
    ws,ds=_ensure_admin_sync_schema(wb); h=[c.value for c in ws[1]]; rid=str(p.get("result_id","")).strip()
    if not rid: raise ValueError("Missing result_id")
    vals={"Result ID":rid,"Student ID":str(p.get("student_id","")),"Student Name":str(p.get("student_name","")),"Student Email":str(p.get("student_email","")),"Exam ID":str(p.get("exam_id","")),"Subject Name":str(p.get("subject_name","")),"Subject Code":str(p.get("subject_code","")),"Total Questions":int(p.get("total_questions",0) or 0),"Correct Answers":int(p.get("correct_answers",0) or 0),"Wrong Answers":int(p.get("wrong_answers",0) or 0),"Score":str(p.get("score","")),"Percentage":float(p.get("percentage",0) or 0),"Recording File":_safe_sync_filename(p.get("recording_file")) if p.get("recording_file") else "","Exam Status":str(p.get("exam_status","Completed")),"Unattempted Answers":int(p.get("unattempted_answers",0) or 0),"Submitted At":str(p.get("submitted_at",""))}
    rc=h.index("Result ID")+1; existing=next((r for r in range(2,ws.max_row+1) if ws.cell(r,rc).value==rid),None)
    if existing is None:
        row=[None]*len(h)
        for k,v in vals.items(): row[h.index(k)]=v
        ws.append(row)
    else:
        for k,v in vals.items(): ws.cell(existing,h.index(k)+1,v)
        h2=[c.value for c in ds[1]]; dc=h2.index("Result ID")+1
        for r in range(ds.max_row,1,-1):
            if ds.cell(r,dc).value==rid: ds.delete_rows(r,1)
    h2=[c.value for c in ds[1]]
    for q in p.get("details") or []:
        qv={"Result ID":rid,"Student ID":vals["Student ID"],"Student Name":vals["Student Name"],"Exam ID":vals["Exam ID"],"Subject Name":vals["Subject Name"],"Subject Code":vals["Subject Code"],"Question Number":q.get("number",""),"Question":q.get("question",""),"Student Answer":q.get("selected_answer",""),"Correct Answer":q.get("correct_answer",""),"Status":q.get("status","")}; row=[None]*len(h2)
        for k,v in qv.items(): row[h2.index(k)]=v
        ds.append(row)

@app.route("/internal/sync/recording", methods=["POST"])
def internal_sync_recording():
    if not _sync_token_valid(request.headers.get("X-ExamGuard-Sync-Token","")): return jsonify({"success":False,"error":"Unauthorized recording sync"}),401
    temp=None
    try:
        exam_id=str(request.form.get("exam_id","")).strip(); student_id=str(request.form.get("student_id","")).strip(); up=request.files.get("recording"); fn=_safe_sync_filename(request.form.get("filename",""))
        if not exam_id or not student_id or not up: return jsonify({"success":False,"error":"Missing recording data"}),400
        os.makedirs(RECORDINGS_FOLDER,exist_ok=True); target=os.path.join(RECORDINGS_FOLDER,fn); temp=target+".uploading"; up.save(temp)
        with open(temp,"rb") as fh: magic=fh.read(4)
        if os.path.getsize(temp)<1024 or magic!=bytes((0x1a,0x45,0xdf,0xa3)):
            os.remove(temp); temp=None; return jsonify({"success":False,"error":"Invalid WebM recording"}),400
        os.replace(temp,target); temp=None
        print(f"[SYNC] Recording received: {fn} ({student_id}/{exam_id})")
        return jsonify({"success":True,"filename":fn,"size":os.path.getsize(target)})
    except Exception as e:
        if temp:
            try: os.remove(temp)
            except OSError: pass
        return jsonify({"success":False,"error":str(e)}),500

@app.route("/internal/sync/result", methods=["POST"])
def internal_sync_result():
    if not _sync_token_valid(request.headers.get("X-ExamGuard-Sync-Token","")): return jsonify({"success":False,"error":"Unauthorized result sync"}),401
    wb=None
    try:
        payload=request.get_json(silent=True) or {}; wb=load_database(); _upsert_admin_sync_result(wb,payload); save_database(wb); wb.close(); return jsonify({"success":True,"result_id":payload.get("result_id","")})
    except Exception as e:
        try: wb.close()
        except Exception: pass
        return jsonify({"success":False,"error":str(e)}),500

@app.route("/internal/sync/recording-chunk", methods=["POST"])
def internal_sync_recording_chunk():
    if not _sync_token_valid(request.headers.get("X-ExamGuard-Sync-Token", "")):
        return jsonify({"success": False, "error": "Unauthorized recording sync"}), 401
    try:
        exam_id = str(request.form.get("exam_id", "")).strip()
        student_id = str(request.form.get("student_id", "")).strip()
        filename = _safe_sync_filename(request.form.get("filename", ""))
        token = str(request.form.get("recording_token", "")).strip()
        seq_raw = str(request.form.get("sequence", "")).strip()
        chunk = request.files.get("chunk")
        if not exam_id or not student_id or not chunk or not token or not seq_raw.isdigit():
            return jsonify({"success": False, "error": "Missing recording chunk data"}), 400
        seq = int(seq_raw)
        if not re.fullmatch(r"[A-Za-z0-9_-]{16,80}", token) or seq < 0 or seq > 1000000:
            return jsonify({"success": False, "error": "Invalid recording chunk metadata"}), 400
        token_dir = os.path.join(RECORDING_PARTS_FOLDER, token)
        os.makedirs(token_dir, exist_ok=True)
        meta_path = os.path.join(token_dir, "meta.json")
        safe_student = re.sub(r"[^A-Za-z0-9._-]+", "_", student_id)[:100] or "student"
        if os.path.exists(meta_path):
            try:
                meta = json.loads(open(meta_path, "r", encoding="utf-8").read())
            except Exception:
                meta = {}
        else:
            meta = {}
        if meta and (str(meta.get("student_id", "")) != student_id or str(meta.get("exam_id", "")) != exam_id):
            return jsonify({"success": False, "error": "Recording token collision"}), 409
        meta.update({"token": token, "student_id": student_id, "exam_id": exam_id, "filename": filename, "updated_at": time.time()})
        tmp_meta = meta_path + ".tmp"
        with open(tmp_meta, "w", encoding="utf-8") as fh: json.dump(meta, fh)
        os.replace(tmp_meta, meta_path)
        part_path = os.path.join(token_dir, f"{seq:08d}.part")
        if not os.path.isfile(part_path):
            temp = part_path + ".uploading"
            chunk.save(temp)
            if os.path.getsize(temp) <= 0:
                os.remove(temp)
                return jsonify({"success": False, "error": "Empty recording chunk"}), 400
            os.replace(temp, part_path)
        progressive = os.path.join(RECORDINGS_FOLDER, filename + ".partial.webm")
        seq_marker = os.path.join(token_dir, "assembled_seq.txt")
        try:
            next_seq = int(Path(seq_marker).read_text(encoding="utf-8").strip() or "0") if os.path.isfile(seq_marker) else 0
            with open(progressive, "ab") as assembled:
                while os.path.isfile(os.path.join(token_dir, f"{next_seq:08d}.part")):
                    part = os.path.join(token_dir, f"{next_seq:08d}.part")
                    with open(part, "rb") as src_file:
                        shutil.copyfileobj(src_file, assembled, length=1024*1024)
                    try: os.remove(part)
                    except OSError: pass
                    next_seq += 1
            tmp_marker = seq_marker + ".tmp"
            Path(tmp_marker).write_text(str(next_seq), encoding="utf-8")
            os.replace(tmp_marker, seq_marker)
        except Exception as inc_exc:
            print("[SYNC] incremental recording assembly warning:", inc_exc)
        return jsonify({"success": True, "filename": filename, "sequence": seq})
    except Exception as e:
        print("[SYNC] recording chunk error:", e)
        return jsonify({"success": False, "error": str(e)}), 500


@app.route("/internal/sync/recording-finalize", methods=["POST"])
def internal_sync_recording_finalize():
    if not _sync_token_valid(request.headers.get("X-ExamGuard-Sync-Token", "")):
        return jsonify({"success": False, "error": "Unauthorized recording sync"}), 401
    try:
        exam_id = str(request.form.get("exam_id", "")).strip()
        student_id = str(request.form.get("student_id", "")).strip()
        filename = _safe_sync_filename(request.form.get("filename", ""))
        token = str(request.form.get("recording_token", "")).strip()
        expected_raw = str(request.form.get("expected_last_seq", "")).strip()
        expected = int(expected_raw) if expected_raw.isdigit() else None
        if not exam_id or not student_id or not token:
            return jsonify({"success": False, "error": "Missing recording finalize data"}), 400
        token_dir = os.path.join(RECORDING_PARTS_FOLDER, token)
        meta_path = os.path.join(token_dir, "meta.json")
        if not os.path.isdir(token_dir) or not os.path.isfile(meta_path):
            return jsonify({"success": False, "error": "Recording chunks not found", "retry": True}), 409
        meta = json.loads(open(meta_path, "r", encoding="utf-8").read())
        if str(meta.get("student_id", "")) != student_id or str(meta.get("exam_id", "")) != exam_id:
            return jsonify({"success": False, "error": "Recording metadata mismatch"}), 403
        target = os.path.join(RECORDINGS_FOLDER, filename)
        partial = target + ".uploading"
        progressive = target + ".partial.webm"
        next_seq = 0
        while os.path.isfile(os.path.join(token_dir, f"{next_seq:08d}.part")):
            next_seq += 1
        if expected is not None and next_seq <= expected:
            return jsonify({"success": False, "retry": True, "next_seq": next_seq,
                            "missing_sequences": list(range(next_seq, min(expected + 1, next_seq + 80))) }), 409
        if next_seq == 0:
            return jsonify({"success": False, "error": "Recording is empty", "retry": True}), 409
        if os.path.isfile(progressive) and os.path.getsize(progressive) >= 1024:
            shutil.copy2(progressive, partial)
        else:
            with open(partial, "wb") as out_file:
                for seq in range(next_seq):
                    part = os.path.join(token_dir, f"{seq:08d}.part")
                    if not os.path.isfile(part):
                        return jsonify({"success": False, "retry": True, "missing_sequences": [seq]}), 409
                    with open(part, "rb") as src_file:
                        shutil.copyfileobj(src_file, out_file, length=1024 * 1024)
        if os.path.getsize(partial) < 1024:
            try: os.remove(partial)
            except OSError: pass
            return jsonify({"success": False, "error": "Recording file too small", "retry": True}), 409
        with open(partial, "rb") as fh:
            magic = fh.read(4)
        if magic != bytes((0x1a, 0x45, 0xdf, 0xa3)):
            try: os.remove(partial)
            except OSError: pass
            return jsonify({"success": False, "error": "Recording is not a valid WebM"}), 400
        if not os.path.isfile(target):
            os.replace(partial, target)
        else:
            try: os.remove(partial)
            except OSError: pass
        try:
            if os.path.isfile(progressive): os.remove(progressive)
        except OSError: pass
        shutil.rmtree(token_dir, ignore_errors=True)
        print(f"[SYNC] Recording finalized on admin: {filename} ({student_id}/{exam_id})")
        return jsonify({"success": True, "filename": filename, "size": os.path.getsize(target)})
    except Exception as e:
        print("[SYNC] recording finalize error:", e)
        try:
            if os.path.isfile(partial): os.remove(partial)
        except Exception:
            pass
        return jsonify({"success": False, "error": str(e)}), 500


@app.route("/internal/sync/live-heartbeat", methods=["POST"])
def internal_sync_live_heartbeat():
    token = str(request.headers.get("X-ExamGuard-Live-Token", "")).strip()
    if not LIVE_SYNC_TOKEN or token != LIVE_SYNC_TOKEN:
        return jsonify({"success":False,"error":"Unauthorized live heartbeat"}),401
    try:
        student_id=str(request.form.get("student_id","")).strip()
        if not student_id:
            return jsonify({"success":False,"error":"Missing student id"}),400
        safe_id=re.sub(r"[^A-Za-z0-9_-]","_",student_id)[:120] or "student"
        os.makedirs(LIVE_FRAMES_FOLDER,exist_ok=True)
        status={
            "student_id":student_id,
            "student_name":str(request.form.get("student_name","")),
            "exam_id":str(request.form.get("exam_id","")),
            # FIX: this used to trust whatever "last_seen" timestamp
            # the STUDENT's own machine sent in the request
            # ("last_seen": time.time() on student_app.py, then
            # echoed back here almost verbatim). get_active_live_
            # sessions() below compares that value against THIS
            # server's own time.time() to decide whether a session is
            # still "live" (within the last 8 seconds). Across two
            # separate computers those clocks are essentially never
            # perfectly in sync, and any client-side lag/drift makes
            # that comparison meaningless — for the direction it
            # actually caused (student's clock running fast, or a
            # heartbeat delayed in transit), it kept a session looking
            # "recent" long after it had actually stopped, leaving a
            # blank/frozen tile in Live Monitoring that would never
            # clear on its own. Always stamping with the receiving
            # server's own clock, at the moment it actually arrives,
            # makes "how long ago was this admin's" a single-clock
            # measurement — no cross-machine skew possible.
            "last_seen":time.time(),
            "student_signal_base_url":str(request.form.get("student_signal_base_url", "")).strip(),
        }
        tmp=os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}.json.uploading")
        with open(tmp,"w",encoding="utf-8") as fh: json.dump(status,fh)
        os.replace(tmp,os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}.json"))
        print(f"[LIVE] heartbeat received: {student_id} / {status["exam_id"]}")
        return jsonify({"success":True})
    except Exception as e:
        try:
            if os.path.exists(tmp): os.remove(tmp)
        except Exception: pass
        return jsonify({"success":False,"error":str(e)}),500

@app.route("/internal/sync/live-frame", methods=["POST"])
def internal_sync_live_frame():
    if not LIVE_SYNC_TOKEN or request.headers.get("X-ExamGuard-Sync-Token","") != LIVE_SYNC_TOKEN:
        return jsonify({"success":False,"error":"Unauthorized live sync"}),401
    temp=None
    try:
        student_id=str(request.form.get("student_id","" )).strip()
        if not student_id or "frame" not in request.files:
            return jsonify({"success":False,"error":"Missing live frame data"}),400
        safe_id=re.sub(r"[^A-Za-z0-9_-]","_",student_id)[:120] or "student"
        os.makedirs(LIVE_FRAMES_FOLDER,exist_ok=True)
        target=os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}.jpg"); temp=target+".uploading"
        request.files["frame"].save(temp)
        with open(temp,"rb") as fh: magic=fh.read(3)
        if os.path.getsize(temp)<256 or magic[:2] != b"\xff\xd8":
            os.remove(temp); temp=None; return jsonify({"success":False,"error":"Invalid JPEG live frame"}),400
        os.replace(temp,target); temp=None
        status={
            "student_id":student_id,
            "student_name":str(request.form.get("student_name","")),
            "exam_id":str(request.form.get("exam_id","")),
            # FIX: same clock-skew issue as the heartbeat endpoint
            # above — always stamp with this server's own receipt
            # time, never a timestamp supplied by the student's own
            # machine, so "how recently was this frame received"
            # can't be thrown off by the two computers' clocks
            # disagreeing.
            "last_seen":time.time(),
            "status":str(request.form.get("status","")),
            "warning":str(request.form.get("warning","false")).lower() in ("1","true","yes","on"),
            "warning_message":str(request.form.get("warning_message","")),
            "student_signal_base_url":str(request.form.get("student_signal_base_url", "")).strip(),
        }
        status_tmp=os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}.json.uploading")
        with open(status_tmp,"w",encoding="utf-8") as fh: json.dump(status,fh)
        os.replace(status_tmp,os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}.json"))
        print(f"[LIVE] frame received: {student_id} / {status["exam_id"]}")
        return jsonify({"success":True})
    except Exception as e:
        if temp:
            try: os.remove(temp)
            except OSError: pass
        return jsonify({"success":False,"error":str(e)}),500

@app.route("/internal/sync/live-audio", methods=["POST"])
def internal_sync_live_audio():
    if not LIVE_SYNC_TOKEN or request.headers.get("X-ExamGuard-Sync-Token","") != LIVE_SYNC_TOKEN:
        return jsonify({"success":False,"error":"Unauthorized live sync"}),401
    temp=None
    try:
        student_id=str(request.form.get("student_id","" )).strip()
        audio=request.files.get("audio")
        if not student_id or not audio: return jsonify({"success":False,"error":"Missing live audio data"}),400
        safe_id=re.sub(r"[^A-Za-z0-9_-]","_",student_id)[:120] or "student"
        os.makedirs(LIVE_FRAMES_FOLDER,exist_ok=True)
        target=os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}_audio.webm"); temp=target+".uploading"
        audio.save(temp)
        with open(temp,"rb") as fh: magic=fh.read(4)
        if os.path.getsize(temp)<256 or magic != bytes((0x1a,0x45,0xdf,0xa3)):
            os.remove(temp); temp=None; return jsonify({"success":False,"error":"Invalid WebM live audio"}),400
        os.replace(temp,target); temp=None
        return jsonify({"success":True})
    except Exception as e:
        if temp:
            try: os.remove(temp)
            except OSError: pass
        return jsonify({"success":False,"error":str(e)}),500

@app.route("/logout")
def logout():

    session.pop("teacher_id", None)
    session.pop("teacher_name", None)
    session.pop("teacher_email", None)

    return redirect(url_for("index"))



@app.route("/teacher/exam/<exam_id>/results")
@teacher_login_required
@safe_results_route("dashboard")
def teacher_exam_results(exam_id):

    teacher_id = session["teacher_id"]

    workbook = load_database()

    exam_sheet = workbook["Exams"]

    results_sheet = workbook["Results"]

    details_sheet = workbook["ResultDetails"]


    # ========================================================
    # CHECK EXAM BELONGS TO TEACHER
    # ========================================================

    exam_found = False

    subject_name = ""

    subject_code = ""

    teacher_name = ""


    for row in exam_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        if row[0] == exam_id:

            if row[1] == teacher_id:

                exam_found = True

                subject_name = row[3]

                subject_code = row[4]

                teacher_name = row[2]

                break


    if not exam_found:

        workbook.close()

        flash(
            "You are not authorized to view this exam.",
            "error"
        )

        return redirect(
            url_for("dashboard")
        )


    # ========================================================
    # GET STUDENT RESULTS
    # ========================================================

    headers = [cell.value for cell in results_sheet[1]]
    header_index = {name: i for i, name in enumerate(headers) if name is not None}

    def result_value(row, name, default=None):
        idx = header_index.get(name)
        return row[idx] if idx is not None and idx < len(row) else default

    student_results = []

    for row in results_sheet.iter_rows(min_row=2, values_only=True):
        if result_value(row, "Exam ID", "") != exam_id:
            continue

        total = int(result_value(row, "Total Questions", 0) or 0)
        correct = int(result_value(row, "Correct Answers", 0) or 0)
        wrong = int(result_value(row, "Wrong Answers", 0) or 0)
        unattempted = int(result_value(row, "Unattempted Answers", max(0, total - correct - wrong)) or 0)
        recording_file = str(result_value(row, "Recording File", "") or "").strip()
        safe_recording = os.path.basename(recording_file)
        recording_available = bool(safe_recording and os.path.isfile(os.path.join(RECORDINGS_FOLDER, safe_recording)))

        student_results.append({
            "result_id": result_value(row, "Result ID", ""),
            "student_id": result_value(row, "Student ID", ""),
            "student_name": result_value(row, "Student Name", ""),
            "total_questions": total,
            "correct_answers": correct,
            "wrong_answers": wrong,
            "score": result_value(row, "Score", ""),
            "percentage": result_value(row, "Percentage", 0),
            "unattempted_answers": unattempted,
            "exam_status": result_value(row, "Exam Status", "Completed") or "Completed",
            "recording_file": safe_recording,
            "recording_available": recording_available,
            "recording_url": url_for("admin_stream_recording", filename=safe_recording) if recording_available else "",
            "recording_download_url": url_for("admin_download_recording", filename=safe_recording) if recording_available else "",
        })


    # ========================================================
    # GET ALL QUESTION DETAILS
    # ========================================================

    details = {}


    for row in details_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        result_exam_id = row[3]


        if result_exam_id == exam_id:

            result_id = row[0]


            if result_id not in details:

                details[result_id] = []


            details[result_id].append({

                "question_number": row[6],

                "question": row[7],

                "student_answer": row[8],

                "correct_answer": row[9],

                "status": row[10]

            })


    workbook.close()


    return render_template(

        "teacher_results.html",

        exam_id=exam_id,

        subject_name=subject_name,

        subject_code=subject_code,

        teacher_name=teacher_name,

        student_results=student_results,

        details=details

    )



@app.route("/teacher/exam/<exam_id>/download")
@teacher_login_required
@safe_results_route("dashboard")
def download_exam_results(exam_id):

    teacher_id = session["teacher_id"]

    workbook = load_database()

    exam_sheet = workbook["Exams"]

    results_sheet = workbook["Results"]

    details_sheet = workbook["ResultDetails"]


    # ========================================================
    # VERIFY TEACHER OWNS EXAM
    # ========================================================

    exam_found = False

    subject_name = ""

    subject_code = ""


    for row in exam_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        if row[0] == exam_id and row[1] == teacher_id:

            exam_found = True

            subject_name = row[3]

            subject_code = row[4]

            break


    if not exam_found:

        workbook.close()

        flash(
            "Unauthorized exam access.",
            "error"
        )

        return redirect(
            url_for("dashboard")
        )


    # ========================================================
    # CREATE NEW EXCEL WORKBOOK
    # ========================================================

    download_workbook = Workbook()


    # ========================================================
    # SUMMARY SHEET
    # ========================================================

    summary = download_workbook.active

    summary.title = "Student Results"


    summary.append([

        "Student ID",

        "Student Name",

        "Subject",

        "Subject Code",

        "Total Questions",

        "Correct Answers",

        "Wrong Answers",

        "Unattempted Answers",

        "Score",

        "Percentage",

        "Exam Status"

    ])


    # ========================================================
    # ADD STUDENT RESULTS
    # ========================================================

    for row in results_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        if row[3] == exam_id:

            summary.append([

                row[1],

                row[2],

                row[4],

                row[5],

                row[6],

                row[7],

                row[8],

                row[13] if len(row) > 13 and row[13] not in (None, "") else max(0, int(row[6] or 0) - int(row[7] or 0) - int(row[8] or 0)),

                row[9],

                row[10],

                row[12] if len(row) > 12 and row[12] not in (None, "") else "Completed"

            ])


    # ========================================================
    # QUESTION-WISE SHEET
    # ========================================================

    details = download_workbook.create_sheet(
        "Question Wise Answers"
    )


    details.append([

        "Student ID",

        "Student Name",

        "Question Number",

        "Question",

        "Student Answer",

        "Correct Answer",

        "Status"

    ])


    for row in details_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        if row[3] == exam_id:

            details.append([

                row[1],

                row[2],

                row[6],

                row[7],

                row[8],

                row[9],

                row[10]

            ])


    # ========================================================
    # AUTO WIDTH
    # ========================================================

    for sheet in download_workbook.worksheets:

        for column in sheet.columns:

            max_length = 0

            column_letter = column[0].column_letter

            for cell in column:

                try:

                    if cell.value is not None:

                        length = len(str(cell.value))

                        if length > max_length:

                            max_length = length

                except:

                    pass

            sheet.column_dimensions[
                column_letter
            ].width = min(max_length + 2, 60)


    # ========================================================
    # SAVE TEMP FILE
    # ========================================================

    filename = (

        f"{subject_code}_"

        f"{exam_id}_"

        f"Results.xlsx"

    )


    filepath = os.path.join(
        DOWNLOADS_FOLDER,
        filename
    )


    os.makedirs(
        DOWNLOADS_FOLDER,
        exist_ok=True
    )


    download_workbook.save(filepath)


    workbook.close()

    download_workbook.close()


    # ========================================================
    # DOWNLOAD
    # ========================================================

    return send_file(

        filepath,

        as_attachment=True,

        download_name=filename,

        mimetype=
        "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"

    )
# ============================================================
# RUN
# ============================================================


@app.route(
    "/admin/subject/<subject_code>/download"
)
#@admin_login_required
@safe_results_route("admin_dashboard")
def admin_download_subject_results(subject_code):

    workbook = load_database()

    exam_sheet = workbook["Exams"]

    results_sheet = workbook["Results"]

    details_sheet = workbook["ResultDetails"]


    subject_name = ""

    exam_ids = []


    # Find subject exams

    for row in exam_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        if str(row[4]) == str(subject_code):

            subject_name = row[3]

            if row[0] not in exam_ids:

                exam_ids.append(row[0])


    # Create new workbook

    download_workbook = Workbook()


    summary = download_workbook.active

    summary.title = "Student Results"


    summary.append([

        "Student ID",

        "Student Name",

        "Exam ID",

        "Subject",

        "Subject Code",

        "Total Questions",

        "Correct Answers",

        "Wrong Answers",

        "Unattempted Answers",

        "Score",

        "Percentage",

        "Exam Status"

    ])


    # Add results

    for row in results_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        if (
            str(row[5]) == str(subject_code)
            and row[3] in exam_ids
        ):

            summary.append([

                row[1],

                row[2],

                row[3],

                row[4],

                row[5],

                row[6],

                row[7],

                row[8],

                row[9],

                row[10]

            ])


    # Question-wise sheet

    details = download_workbook.create_sheet(
        "Question Wise Answers"
    )


    details.append([

        "Student ID",

        "Student Name",

        "Exam ID",

        "Question Number",

        "Question",

        "Student Answer",

        "Correct Answer",

        "Status"

    ])


    for row in details_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        if str(row[5]) == str(subject_code):

            details.append([

                row[1],

                row[2],

                row[3],

                row[6],

                row[7],

                row[8],

                row[9],

                row[10]

            ])


    # Auto column width

    for sheet in download_workbook.worksheets:

        for column in sheet.columns:

            max_length = 0

            column_letter = column[0].column_letter


            for cell in column:

                if cell.value is not None:

                    max_length = max(
                        max_length,
                        len(str(cell.value))
                    )


            sheet.column_dimensions[
                column_letter
            ].width = min(
                max_length + 2,
                60
            )


    os.makedirs(
        DOWNLOADS_FOLDER,
        exist_ok=True
    )


    filename = (
        f"{subject_code}_"
        f"All_Student_Results.xlsx"
    )


    filepath = os.path.join(
        DOWNLOADS_FOLDER,
        filename
    )


    download_workbook.save(filepath)

    workbook.close()

    download_workbook.close()


    return send_file(

        filepath,

        as_attachment=True,

        download_name=filename,

        mimetype=
        "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"

    )


@app.route(
    "/admin/subject/<subject_code>/results"
)
#@admin_login_required
@safe_results_route("admin_dashboard")
def admin_subject_results(subject_code):

    workbook = load_database()

    exam_sheet = workbook["Exams"]

    results_sheet = workbook["Results"]

    details_sheet = workbook["ResultDetails"]


    subject_name = ""

    exam_ids = []


    # Find exams belonging to subject

    for row in exam_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        if str(row[4]) == str(subject_code):

            subject_name = row[3]

            if row[0] not in exam_ids:

                exam_ids.append(row[0])


    # Get student results

    headers = [cell.value for cell in results_sheet[1]]
    header_index = {name: i for i, name in enumerate(headers) if name is not None}

    def result_value(row, name, default=None):
        idx = header_index.get(name)
        return row[idx] if idx is not None and idx < len(row) else default

    student_results = []

    for row in results_sheet.iter_rows(min_row=2, values_only=True):
        row_subject = str(result_value(row, "Subject Code", ""))
        row_exam = result_value(row, "Exam ID", "")
        if row_subject != str(subject_code) or row_exam not in exam_ids:
            continue

        total = int(result_value(row, "Total Questions", 0) or 0)
        correct = int(result_value(row, "Correct Answers", 0) or 0)
        wrong = int(result_value(row, "Wrong Answers", 0) or 0)
        unattempted = int(result_value(row, "Unattempted Answers", max(0, total - correct - wrong)) or 0)
        recording_file = os.path.basename(str(result_value(row, "Recording File", "") or "").strip())
        available = bool(recording_file and os.path.isfile(os.path.join(RECORDINGS_FOLDER, recording_file)))

        student_results.append({
            "result_id": result_value(row, "Result ID", ""),
            "student_id": result_value(row, "Student ID", ""),
            "student_name": result_value(row, "Student Name", ""),
            "exam_id": row_exam,
            "subject_name": result_value(row, "Subject Name", ""),
            "subject_code": row_subject,
            "total_questions": total,
            "correct_answers": correct,
            "wrong_answers": wrong,
            "score": result_value(row, "Score", ""),
            "percentage": result_value(row, "Percentage", 0),
            "unattempted_answers": unattempted,
            "exam_status": result_value(row, "Exam Status", "Completed") or "Completed",
            "recording_file": recording_file,
            "recording_available": available,
            "recording_url": url_for("admin_stream_recording", filename=recording_file) if available else "",
            "recording_download_url": url_for("admin_download_recording", filename=recording_file) if available else "",
        })


    # Get question-wise answers

    details = {}


    for row in details_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        if str(row[5]) == str(subject_code):

            result_id = row[0]


            if result_id not in details:

                details[result_id] = []


            details[result_id].append({

                "question_number": row[6],

                "question": row[7],

                "student_answer": row[8],

                "correct_answer": row[9],

                "status": row[10]

            })


    workbook.close()


    return render_template(

        "admin_subject_results.html",

        subject_name=subject_name,

        subject_code=subject_code,

        student_results=student_results,

        details=details

    )


@app.route("/admin/dashboard")
#@admin_login_required
def admin_dashboard():

    workbook = load_database()

    exam_sheet = workbook["Exams"]

    subjects = {}


    for row in exam_sheet.iter_rows(
        min_row=2,
        values_only=True
    ):

        exam_id = row[0]

        teacher_id = row[1]

        teacher_name = row[2]

        subject_name = row[3]

        subject_code = row[4]


        key = subject_code


        if key not in subjects:

            subjects[key] = {

                "subject_code": subject_code,

                "subject_name": subject_name,

                "teacher_names": set(),

                "exam_ids": []

            }


        subjects[key]["teacher_names"].add(
            teacher_name
        )


        if exam_id not in subjects[key]["exam_ids"]:

            subjects[key]["exam_ids"].append(
                exam_id
            )


    workbook.close()


    # Convert set to string

    for subject in subjects.values():

        subject["teacher_names"] = ", ".join(
            subject["teacher_names"]
        )


    return render_template(

        "admin_dashboard.html",

        subjects=list(subjects.values())

    )


@app.route("/admin/login", methods=["GET", "POST"])
def admin_login():

    if request.method == "POST":

        admin_id = request.form["admin_id"].strip()
        password = request.form["password"]

        workbook = load_database()

        sheet = workbook["Admins"]

        admin_found = False

        for row in sheet.iter_rows(
            min_row=2,
            values_only=True
        ):

            if (
                str(row[0]) == admin_id
                and str(row[3]) == password
            ):

                session["admin_id"] = row[0]
                session["admin_name"] = row[1]
                session["admin_email"] = row[2]

                admin_found = True

                break

        workbook.close()

        if admin_found:

            return redirect(
                url_for("admin_dashboard")
            )

        flash(
            "Invalid Admin ID or password.",
            "error"
        )

    return render_template(
        "admin_login.html"
    )


# ==========================================
# ADMIN LOGOUT
# ==========================================




@app.route("/admin/register", methods=["GET", "POST"])
def admin_register():

    if request.method == "POST":

        admin_id = request.form["admin_id"].strip()

        admin_name = request.form["admin_name"].strip()

        email = request.form["email"].strip()

        password = request.form["password"]


        workbook = load_database()

        sheet = workbook["Admins"]


        # Check duplicate Admin ID

        for row in sheet.iter_rows(
            min_row=2,
            values_only=True
        ):

            if str(row[0]) == admin_id:

                workbook.close()

                flash(
                    "Admin ID already exists.",
                    "error"
                )

                return redirect(
                    url_for("admin_register")
                )


        # Save admin

        sheet.append([
            admin_id,
            admin_name,
            email,
            password
        ])


        save_database(workbook)

        workbook.close()


        flash(
            "Admin registration successful.",
            "success"
        )


        return redirect(
            url_for("admin_login")
        )


    return render_template(
        "admin_register.html"
    )




@app.route("/admin/logout")
def admin_logout():

    session.pop("admin_id", None)
    session.pop("admin_name", None)
    session.pop("admin_email", None)

    flash("Admin logged out successfully.", "success")

    return redirect(url_for("index"))
# ============================================================
# EXAM VIDEO RECORDING UPLOAD
# ============================================================


@app.route("/admin/exam/<exam_id>/recordings")
def admin_exam_recordings(exam_id):
    """
    FIX: this used to build its file list from a raw folder scan
    ("any .webm file whose name happens to contain this exam_id"),
    plus a loose secondary scan of the Results sheet. A substring
    match like that will also match older/leftover recording files
    from before recordings used one stable filename per (student,
    exam) — so old, no-longer-current files kept showing up
    alongside the real one for the same student ("previous
    recordings also"). Since a student can only complete a given
    exam once, the Results sheet already has exactly one row (and
    therefore, if present, exactly one recording) per student for
    this exam — so that's now the single source of truth: one entry
    per completed result row, carrying the student's name, email,
    subject, and submission time right alongside the recording, and
    never anything stray.
    """

    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    entries = []
    subject_name = ""
    try:
        wb = load_database(read_only=True, data_only=True)
        if "Results" in wb.sheetnames:
            ws = wb["Results"]
            headers = [c.value for c in ws[1]]
            hi = {name: i for i, name in enumerate(headers) if name is not None}
            ei = hi.get("Exam ID")
            if ei is not None:
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if ei >= len(row) or row[ei] != exam_id:
                        continue

                    def cell(col_name, default=""):
                        idx = hi.get(col_name)
                        if idx is None or idx >= len(row) or row[idx] is None:
                            return default
                        return row[idx]

                    subject_name = cell("Subject Name", subject_name) or subject_name
                    recording_name = os.path.basename(str(cell("Recording File", "")).strip())
                    recording_path = os.path.join(RECORDINGS_FOLDER, recording_name) if recording_name else ""
                    entries.append({
                        "student_id": cell("Student ID", ""),
                        "student_name": cell("Student Name", "Unknown"),
                        "student_email": cell("Student Email", ""),
                        "subject_name": cell("Subject Name", ""),
                        "submitted_at": cell("Submitted At", ""),
                        "percentage": cell("Percentage", ""),
                        "exam_status": cell("Exam Status", ""),
                        "filename": recording_name if (recording_name and os.path.isfile(recording_path)) else "",
                        "recording_missing": bool(recording_name) and not os.path.isfile(recording_path),
                    })
        wb.close()
    except Exception as e:
        print("Admin recording lookup warning:", e)

    # Oldest-attempt-first is confusing on a results-style page; show most
    # recently submitted first, same ordering feel as the old file listing.
    entries.sort(key=lambda e: str(e.get("submitted_at", "")), reverse=True)

    # Kept for any code/template still expecting a flat filename list.
    files = [e["filename"] for e in entries if e["filename"]]

    return render_template(
        "admin_recordings.html",
        exam_id=exam_id,
        subject_name=subject_name,
        entries=entries,
        files=files
    )


@app.route("/admin/recordings")
def admin_recordings():
    """
    FIX: this used to just list every .webm file sitting in
    RECORDINGS_FOLDER, for every student and every exam, all mixed
    together on one page — clicking "Exam Recordings" from the
    dashboard gave you everyone's recordings at once instead of one
    student's. admin_exam_recordings() (the /admin/exam/<exam_id>/
    recordings route) already does this correctly: one card per
    student, each tied to that student's own Results row and only
    that student's recording. So this page is now just an index of
    exams — pick an exam here, land on that already-correct
    per-student page. No raw folder listing anymore.
    """

    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    exams = {}
    try:
        wb = load_database(read_only=True, data_only=True)
        if "Results" in wb.sheetnames:
            ws = wb["Results"]
            headers = [c.value for c in ws[1]]
            hi = {name: i for i, name in enumerate(headers) if name is not None}
            ei = hi.get("Exam ID")
            si = hi.get("Subject Name")
            if ei is not None:
                for row in ws.iter_rows(min_row=2, values_only=True):
                    if ei >= len(row) or not row[ei]:
                        continue
                    exam_id = str(row[ei])
                    subject_name = ""
                    if si is not None and si < len(row) and row[si]:
                        subject_name = str(row[si])
                    entry = exams.setdefault(exam_id, {"subject_name": subject_name, "count": 0})
                    if subject_name:
                        entry["subject_name"] = subject_name
                    entry["count"] += 1
        wb.close()
    except Exception as e:
        print("Admin recordings index warning:", e)

    cards = "".join(
        f"<div class='card'><b>{exam_id}</b>"
        f"{' &middot; ' + info['subject_name'] if info['subject_name'] else ''}"
        f"<div style='color:#8a8398;font-size:13px;margin-top:4px'>{info['count']} result(s)</div>"
        f"<a href='{url_for('admin_exam_recordings', exam_id=exam_id)}'>View recordings</a></div>"
        for exam_id, info in sorted(exams.items())
    )

    if not cards:
        cards = "<p>No exam results yet.</p>"

    html = f"""
    <!doctype html>
    <html>
    <head>
      <title>Exam Recordings</title>
      <style>
        body{{font-family:'Segoe UI',Arial,sans-serif;background:#faf8f5;color:#201a2e;padding:30px}}
        h1{{font-family:'Segoe UI',Arial,sans-serif}}
        .card{{background:#ffffff;border:1px solid #e7e1f2;padding:18px;margin:14px 0;border-radius:10px}}
        a{{display:inline-block;margin-top:12px;padding:8px 14px;background:#7c5cff;color:white;text-decoration:none;border-radius:6px;font-weight:600;font-size:13px}}
      </style>
    </head>
    <body>
      <h1>Exam Recordings</h1>
      <p style="color:#655f73">Pick an exam to see recordings for that exam only — one entry per student, with only their own recording.</p>
      {cards}
      <p><a href='{url_for("admin_dashboard")}' style="background:#e7e1f2">Back to Admin Dashboard</a></p>
    </body>
    </html>
    """

    return html




@app.route("/admin/recording/<path:filename>")
def admin_download_recording(filename):

    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    safe_name = os.path.basename(filename)

    filepath = os.path.join(
        RECORDINGS_FOLDER,
        safe_name
    )

    if not os.path.isfile(filepath):
        return "Recording not found", 404

    return send_from_directory(
        RECORDINGS_FOLDER,
        safe_name,
        as_attachment=True
    )




@app.route("/admin/recording-stream/<path:filename>")
def admin_stream_recording(filename):
    """Streams the video inline (with seek support) so it plays in a <video> tag,
    instead of forcing a download like admin_download_recording does."""

    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    safe_name = os.path.basename(filename)

    filepath = os.path.join(
        RECORDINGS_FOLDER,
        safe_name
    )

    if not os.path.isfile(filepath):
        return "Recording not found", 404

    return send_from_directory(
        RECORDINGS_FOLDER,
        safe_name,
        as_attachment=False,
        mimetype="video/webm",
        conditional=True
    )





# ============================================================
# LIVE STUDENT MONITORING
#
# The student app (student_app.py) saves each student's latest
# webcam frame + status to the shared live_frames/ folder while
# they take an exam. This app reads those same files — even
# though it's a completely separate process, possibly on a
# completely separate computer sharing the same project folder
# over a network drive, or (more commonly for this project)
# both apps running on one machine while other computers just
# view the browser pages over the network.
#
# A student is considered "currently live" if their status file
# was updated within the last 8 seconds (monitor_exam runs
# roughly every 1.5s while the exam page is open).
# ============================================================

LIVE_ACTIVE_WINDOW_SECONDS = 8


def get_active_live_sessions():
    """Return exactly one active session per student."""
    if not os.path.isdir(LIVE_FRAMES_FOLDER): return []
    now=time.time(); newest={}
    for filename in os.listdir(LIVE_FRAMES_FOLDER):
        if not filename.endswith(".json") or filename.endswith(".uploading"): continue
        path=os.path.join(LIVE_FRAMES_FOLDER,filename)
        try:
            with open(path,"r",encoding="utf-8") as fh: data=json.load(fh)
            sid=str(data.get("student_id","")).strip(); seen=float(data.get("last_seen",0) or 0)
        except Exception: continue
        if not sid or now-seen>LIVE_ACTIVE_WINDOW_SECONDS: continue
        if sid not in newest or seen>=float(newest[sid].get("last_seen",0) or 0): newest[sid]=data
    result=list(newest.values()); result.sort(key=lambda x:str(x.get("student_name","")))
    return result


@app.route("/admin/live")
def admin_live():
    if "admin_id" not in session:
        return redirect(url_for("admin_login"))
    html = r"""
    <!doctype html>
    <html>
    <head>
      <title>Live Exam Monitoring</title>
      <style>
        body{font-family:'Segoe UI',Arial,sans-serif;background:#0a0e1a;color:#f1f0f7;padding:30px;margin:0}
        h1{font-size:22px;margin-bottom:4px}.sub{color:#a7a2bd;font-size:13.5px;margin-bottom:18px}
        #grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(280px,1fr));gap:16px}
        .card{background:#141a2c;border:1px solid rgba(255,255,255,.1);border-radius:10px;overflow:hidden;cursor:pointer}
        .card:hover{border-color:#9d85ff}.live-img{width:100%;height:200px;object-fit:cover;display:block;background:#000}
        .meta{padding:12px 14px}.name{font-weight:600;font-size:14px}.student-exam{color:#9891ab;font-size:11.5px;margin-top:2px;font-family:monospace}
        .status{font-size:12px;margin-top:5px;padding:2px 8px;border-radius:12px;display:inline-block}
        .status-normal{background:#143322;color:#4ade80;border:1px solid #245c3a}.status-warning{background:#32191d;color:#f87171;border:1px solid #5c2a2a}
        #empty{color:#9891ab;padding:60px 0;text-align:center}.back{color:#9d85ff;text-decoration:none;font-size:13.5px}
        #voicebar{display:flex;gap:10px;align-items:center;flex-wrap:wrap;background:#141a2c;border:1px solid rgba(157,133,255,.3);border-radius:12px;padding:14px 16px;margin:16px 0 22px}
        #voiceBtn{background:#9d85ff;color:#fff;border:0;padding:11px 18px;border-radius:8px;font-weight:700;cursor:pointer}
        #voiceBtn.on{background:#4ade80;color:#07130b}.muted{color:#a7a2bd;font-size:12.5px}.live-dot{width:9px;height:9px;border-radius:50%;background:#4ade80;display:inline-block;margin-right:6px}
        .image-state{position:absolute;left:10px;top:10px;background:rgba(0,0,0,.65);padding:4px 8px;border-radius:6px;font:600 11px monospace}
        .image-wrap{position:relative;background:#000}
      </style>
    </head>
    <body>
      <a class="back" href="/admin/dashboard">&larr; Back to Admin Dashboard</a>
      <h1 style="margin-top:16px">Live Exam Monitoring</h1>
      <div class="sub">One live card per active student. Camera preview is separate from AI analysis.</div>
      <div id="voicebar">
        <button id="voiceBtn">🎙 Start Speaking to Students</button>
       <button id="audioBtn" style="margin-left:10px;background:#19a974">🔊 Enable Student Audio</button>
        <span id="voiceStatus" class="muted"><span class="live-dot"></span>Voice broadcast is off</span>
      </div>
      <div id="grid"></div>
      <div id="empty" style="display:none">No students are currently taking an exam.</div>
      <script>
        const voicePeerConnections = new Map();
        const videoPeerConnections = new Map();
        const videoOfferBusy = new Set();
        const videoOfferTimers = new Map();
        let adminMicStream = null, voiceRunning = false, refreshBusy = false, studentAudioEnabled = false;
        const grid = document.getElementById('grid');
        const empty = document.getElementById('empty');
        const voiceBtn = document.getElementById('voiceBtn');
        const voiceStatus = document.getElementById('voiceStatus');

        function setVoiceStatus(text){ voiceStatus.innerHTML='<span class="live-dot"></span>'+text; }
        function safeDomId(id){ return 'live-card-'+String(id).replace(/[^A-Za-z0-9_-]/g,'_'); }
        function waitIce(pc, timeoutMs=5000){
          if(pc.iceGatheringState==='complete') return Promise.resolve();
          return new Promise(resolve=>{
            let done=false;
            const finish=()=>{if(done)return;done=true;clearTimeout(timer);pc.removeEventListener('icegatheringstatechange',check);resolve();};
            const check=()=>{if(pc.iceGatheringState==='complete')finish();};
            const timer=setTimeout(finish,timeoutMs);
            pc.addEventListener('icegatheringstatechange',check); check();
          });
        }

        async function startVideoPeer(s){
          const id=String(s.student_id||'').trim(), exam=String(s.exam_id||'').trim();
          if(!id || !exam || videoOfferBusy.has(id)) return;
          const old=videoPeerConnections.get(id);
          if(old && ['connected','connecting'].includes(old.connectionState)) return;
          videoOfferBusy.add(id);
          try{
            if(old){try{old.close();}catch(e){} videoPeerConnections.delete(id);}
            const pc=new RTCPeerConnection({iceServers:[]});
            videoPeerConnections.set(id,pc);
            pc.addTransceiver('video',{direction:'recvonly'});
             pc.addTransceiver('audio',{direction:'recvonly'});
            const img=document.getElementById('live-img-'+id.replace(/[^A-Za-z0-9_-]/g,'_'));
            if(img){
              const v=document.createElement('video');
              v.className='live-img'; v.autoplay=true; v.playsInline=true; v.muted=!studentAudioEnabled;
              v.id=img.id; v.dataset.studentVideo='1';
              img.replaceWith(v);
            }
            const video=document.getElementById('live-img-'+id.replace(/[^A-Za-z0-9_-]/g,'_'));
            // Keep one remote MediaStream per student so the same <video> element
            // receives BOTH the camera track and microphone track. Some browsers
            // fire ontrack separately for audio and video; replacing srcObject
            // with a one-track stream would make the other track disappear.
            const remoteStream=new MediaStream();
            pc.ontrack=e=>{
              const track=e.track;
              if(track && !remoteStream.getTracks().some(t=>t.id===track.id)){
                remoteStream.addTrack(track);
              }
              if(video){
                video.srcObject=remoteStream;
                video.muted=!studentAudioEnabled;
                video.volume=1.0;
                video.play().catch(()=>{});
              }
              const st=document.getElementById('image-state-'+id.replace(/[^A-Za-z0-9_-]/g,'_'));
              if(st){
                const hasVideo=remoteStream.getVideoTracks().length>0;
                const hasAudio=remoteStream.getAudioTracks().length>0;
                st.textContent=hasVideo && hasAudio ? '● LIVE CAMERA + AUDIO' : (hasVideo ? '● LIVE CAMERA' : '● LIVE AUDIO');
              }
              console.log('[LIVE WEBRTC]',id,'track:',track ? track.kind : 'unknown');
            };
            pc.onconnectionstatechange=()=>{
              const st=document.getElementById('image-state-'+id.replace(/[^A-Za-z0-9_-]/g,'_'));
              if(['failed','disconnected','closed'].includes(pc.connectionState) && st) st.textContent='RECONNECTING CAMERA';
              if(pc.connectionState==='failed' && videoPeerConnections.get(id)===pc){
                try{pc.close();}catch(e){} videoPeerConnections.delete(id);
                setTimeout(()=>{ if(document.getElementById(safeDomId(id))) startVideoPeer(s); },800);
              }
            };
            const offer=await pc.createOffer();
            await pc.setLocalDescription(offer);
            await waitIce(pc);
            const r=await fetch('/admin/video/offer',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({student_id:id,exam_id:exam,offer:pc.localDescription})});
            const d=await r.json();
            if(!r.ok || !d.success) throw new Error(d.error||('offer HTTP '+r.status));
            pollVideoAnswer(id,pc);
          }catch(e){
            console.debug('[LIVE VIDEO] offer',id,e);
            const st=document.getElementById('image-state-'+id.replace(/[^A-Za-z0-9_-]/g,'_'));
            if(st) st.textContent='WAITING FOR CAMERA';
            const pc=videoPeerConnections.get(id); if(pc){try{pc.close();}catch(_){}}
            videoPeerConnections.delete(id);
          }finally{ videoOfferBusy.delete(id); }
        }

        async function pollVideoAnswer(id,pc){
          for(let n=0;n<25;n++){
            if(videoPeerConnections.get(id)!==pc) return;
            try{
              const r=await fetch('/admin/video/answer/'+encodeURIComponent(id)+'?t='+Date.now(),{cache:'no-store'});
              if(r.ok){const d=await r.json(); if(d.success && d.answer){await pc.setRemoteDescription(new RTCSessionDescription(d.answer)); return;}}
            }catch(e){}
            await new Promise(r=>setTimeout(r,300));
          }
          if(videoPeerConnections.get(id)===pc && pc.connectionState!=='connected'){
            try{pc.close();}catch(e){} videoPeerConnections.delete(id);
          }
        }

        function stopVideoPeer(id){
          const pc=videoPeerConnections.get(id); if(pc){try{pc.close();}catch(e){}}
          videoPeerConnections.delete(id);
        }

        function makeCard(s){
          const id=String(s.student_id||'').trim(); if(!id)return null;
          const cardId=safeDomId(id); let card=document.getElementById(cardId); if(card)return card;
          card=document.createElement('div'); card.className='card'; card.id=cardId; card.dataset.studentId=id;
          card.onclick=()=>location.href='/admin/live/'+encodeURIComponent(id);
          const wrap=document.createElement('div'); wrap.className='image-wrap';
          const video=document.createElement('video');
          video.className='live-img'; video.id='live-img-'+id.replace(/[^A-Za-z0-9_-]/g,'_'); video.autoplay=true; video.playsInline=true; video.muted=true;
          video.poster='';
          const state=document.createElement('div'); state.className='image-state'; state.id='image-state-'+id.replace(/[^A-Za-z0-9_-]/g,'_'); state.textContent='CONNECTING CAMERA';
          wrap.appendChild(video); wrap.appendChild(state);
          const meta=document.createElement('div'); meta.className='meta';
          const nm=document.createElement('div'); nm.className='name'; nm.id='live-name-'+id.replace(/[^A-Za-z0-9_-]/g,'_'); nm.textContent=s.student_name||id;
          const ex=document.createElement('div'); ex.className='student-exam'; ex.id='live-exam-'+id.replace(/[^A-Za-z0-9_-]/g,'_'); ex.textContent=s.exam_id||'';
          const st=document.createElement('span'); st.className='status'; st.id='live-status-'+id.replace(/[^A-Za-z0-9_-]/g,'_');
          meta.appendChild(nm); meta.appendChild(ex); meta.appendChild(st); card.appendChild(wrap); card.appendChild(meta); grid.appendChild(card);
          startVideoPeer(s); return card;
        }

        function updateCard(s){
          const id=String(s.student_id||'').trim(); if(!id)return;
          makeCard(s); const key=id.replace(/[^A-Za-z0-9_-]/g,'_');
          const nm=document.getElementById('live-name-'+key), ex=document.getElementById('live-exam-'+key), st=document.getElementById('live-status-'+key);
          if(nm)nm.textContent=s.student_name||id; if(ex)ex.textContent=s.exam_id||'';
          if(st){const warning=!!s.warning;st.className='status '+(warning?'status-warning':'status-normal');st.textContent=warning?(s.warning_message||'Warning'):'Normal';}
        }

        function removeCard(id){ stopVideoPeer(id); const card=document.getElementById(safeDomId(id)); if(card)card.remove(); }

        // --- Existing admin voice broadcast preserved ---
        async function startVoiceStudent(student){const id=String(student.student_id||'');if(!id||!student.exam_id||voicePeerConnections.has(id))return;const pc=new RTCPeerConnection({iceServers:[{urls:'stun:stun.l.google.com:19302'},{urls:'stun:stun1.l.google.com:19302'}]});voicePeerConnections.set(id,pc);if(adminMicStream)adminMicStream.getTracks().forEach(track=>pc.addTrack(track,adminMicStream));try{const offer=await pc.createOffer();await pc.setLocalDescription(offer);await waitIce(pc);const r=await fetch('/admin/voice/offer',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({student_id:id,exam_id:student.exam_id,offer:pc.localDescription})});const d=await r.json();if(!r.ok||!d.success)throw new Error(d.error||'voice offer failed');}catch(e){try{pc.close();}catch(_){}voicePeerConnections.delete(id);}}
        async function pollVoiceAnswers(){for(const [id,pc] of voicePeerConnections.entries()){if(pc.currentRemoteDescription)continue;try{const r=await fetch('/admin/voice/answer/'+encodeURIComponent(id));const d=await r.json();if(d.success&&d.answer)await pc.setRemoteDescription(new RTCSessionDescription(d.answer));}catch(e){}}}
        async function syncVoiceStudents(){if(!voiceRunning)return;try{const res=await fetch('/admin/live-status',{cache:'no-store'});const ss=await res.json();for(const s of ss)await startVoiceStudent(s);setVoiceStatus(`Broadcast ON — ${voicePeerConnections.size} student connection${voicePeerConnections.size===1?'':'s'}`);}catch(e){setVoiceStatus('Broadcast ON — waiting for students');}}
        async function stopVoice(){voiceRunning=false;for(const [id,pc] of voicePeerConnections.entries()){try{pc.close();}catch(e){}fetch('/admin/voice/stop/'+encodeURIComponent(id),{method:'POST'}).catch(()=>{});}voicePeerConnections.clear();if(adminMicStream)adminMicStream.getTracks().forEach(t=>t.stop());adminMicStream=null;voiceBtn.textContent='🎙 Start Speaking to Students';voiceBtn.classList.remove('on');setVoiceStatus('Voice broadcast is off');}
        async function startVoice(){try{adminMicStream=await navigator.mediaDevices.getUserMedia({audio:true,video:false});voiceRunning=true;voiceBtn.textContent='🔴 Stop Speaking';voiceBtn.classList.add('on');await syncVoiceStudents();}catch(e){alert('Microphone access was not granted.');await stopVoice();}}
        async function waitIce(pc){if(pc.iceGatheringState==='complete')return;await new Promise(resolve=>{const to=setTimeout(resolve,7000);const f=()=>{if(pc.iceGatheringState==='complete'){clearTimeout(to);pc.removeEventListener('icegatheringstatechange',f);resolve();}};pc.addEventListener('icegatheringstatechange',f);});}

        async function refreshGrid(){
          if(refreshBusy) return;
          refreshBusy=true;
          try{
            const res=await fetch('/admin/live-status',{cache:'no-store'});
            const raw=await res.json();
            // Hard dedupe by student ID. Even if a malformed/old status source
            // returns duplicates, the browser can only render one card.
            const byStudent=new Map();
            for(const s of raw){
              const id=String(s.student_id||'').trim();
              if(id) byStudent.set(id,s);
            }
            const sessions=Array.from(byStudent.values());
            const activeIds=new Set(sessions.map(s=>String(s.student_id)));
            empty.style.display=sessions.length?'none':'block';
            for(const s of sessions) updateCard(s);
            for(const card of Array.from(grid.children)){
              const id=String(card.dataset.studentId||'');
              if(id && !activeIds.has(id)) removeCard(id);
            }
          }catch(e){console.error('[LIVE GRID]',e);}finally{refreshBusy=false;}
        }

        const audioBtn = document.getElementById('audioBtn');
         async function enableStudentAudio(){
           studentAudioEnabled=true;
           audioBtn.textContent='🔊 Student Audio ON';
           audioBtn.classList.add('on');
           for(const video of document.querySelectorAll('video[data-student-video="1"], video.live-img')){
             video.muted=false;
             video.volume=1.0;
             try{ await video.play(); }catch(e){ console.debug('[LIVE AUDIO] play',e); }
           }
           console.log('[LIVE AUDIO] student audio playback enabled');
         }
         audioBtn.addEventListener('click',enableStudentAudio);
         voiceBtn.addEventListener('click',()=>voiceRunning?stopVoice():startVoice());
        setInterval(refreshGrid,1000);
        setInterval(syncVoiceStudents,2500);
        setInterval(pollVoiceAnswers,800);
        refreshGrid();
        window.addEventListener('beforeunload',()=>{for(const [id,pc] of voicePeerConnections.entries()){try{pc.close();}catch(e){}}if(voiceRunning)stopVoice();for(const [id,pc] of videoPeerConnections.entries()){try{pc.close();}catch(e){}}videoPeerConnections.clear();});
      </script>
    </body>
    </html>
    """
    return html


@app.route("/admin/live-status")
def admin_live_status():

    if "admin_id" not in session:
        return jsonify([])

    return jsonify(get_active_live_sessions())


@app.route("/admin/live-frame/<student_id>")
def admin_live_frame(student_id):
    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    safe_id=re.sub(r"[^A-Za-z0-9_-]","_",str(student_id))[:120] or "student"
    local_path=os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}.jpg")

    # Read the student's advertised LAN URL from the latest status.
    student_base=""
    try:
        with open(os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}.json"),"r",encoding="utf-8") as fh:
            status=json.load(fh)
        student_base=str(status.get("student_signal_base_url","")).strip().rstrip("/")
    except Exception:
        pass

    # PRIMARY path for two-computer deployments: pull the newest JPEG
    # directly from the student's Flask server. This avoids relying on a
    # shared filesystem and avoids stale admin-side JPEGs.
    if student_base and LIVE_SYNC_TOKEN:
        try:
            r=requests.get(
                f"{student_base}/internal/live-frame/{safe_id}",
                headers={"X-ExamGuard-Sync-Token":LIVE_SYNC_TOKEN},
                timeout=(1.2,2.5),
                verify=STUDENT_SIGNAL_VERIFY_SSL,
            )
            if r.ok and r.content:
                response=app.response_class(r.content,mimetype="image/jpeg")
                response.headers["Cache-Control"]="no-store, no-cache, must-revalidate, max-age=0"
                return response
            print(f"[LIVE PULL] {safe_id}: HTTP {r.status_code}")
        except Exception as exc:
            print(f"[LIVE PULL] {safe_id}: {exc}")

    # FALLBACK path: use a frame that was successfully synced to admin.
    if os.path.isfile(local_path):
        response=send_from_directory(LIVE_FRAMES_FOLDER,f"{safe_id}.jpg",mimetype="image/jpeg")
        response.headers["Cache-Control"]="no-store, no-cache, must-revalidate, max-age=0"
        return response

    return "",404


@app.route("/admin/live/<student_id>")
def admin_live_focus(student_id):

    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    safe_id = "".join(c for c in student_id if c.isalnum() or c in "-_")

    html = f"""
    <!doctype html>
    <html>
    <head>
      <title>Live — {safe_id}</title>
      <style>
        body{{font-family:'Segoe UI',Arial,sans-serif;background:#faf8f5;color:#201a2e;padding:0;margin:0}}
        #topbar{{display:flex;justify-content:space-between;align-items:center;padding:14px 22px;background:#ffffff;border-bottom:1px solid #e7e1f2}}
        #topbar a{{color:#7c5cff;text-decoration:none;font-size:13.5px}}
        #status-pill{{padding:6px 14px;border-radius:20px;font-size:13px;font-weight:600}}
        .status-normal{{background:#ecfdf3;color:#16a34a;border:1px solid #b7ecc8}}
        .status-warning{{background:#fdeef1;color:#e0405c;border:1px solid #f6c3cf}}
        #stage{{display:flex;align-items:center;justify-content:center;padding:30px}}
        #liveimg{{max-width:90vw;max-height:75vh;border-radius:10px;border:1px solid #e7e1f2;background:#000}}
        #fsbtn{{position:fixed;bottom:24px;right:24px;background:#7c5cff;color:#fff;border:none;
                padding:12px 22px;border-radius:8px;font-weight:600;cursor:pointer;font-size:14px}}
        #fsbtn:hover{{background:#4a76e6}}
        #audiobtn{{position:fixed;bottom:24px;right:190px;background:#ffffff;color:#201a2e;
                border:1px solid #e7e1f2;padding:12px 22px;border-radius:8px;font-weight:600;
                cursor:pointer;font-size:14px}}
        #audiobtn.on{{background:#ecfdf3;border-color:#b7ecc8;color:#16a34a}}
        #audiobtn:hover{{border-color:#7c5cff}}
        #stage:fullscreen{{background:#000;display:flex;align-items:center;justify-content:center}}
        #stage:fullscreen #liveimg{{max-width:100vw;max-height:100vh}}
      </style>
    </head>
    <body>
      <div id="topbar">
        <a href="/admin/live">&larr; Back to Live Monitoring</a>
        <span id="status-pill" class="status-normal">Connecting...</span>
      </div>
      <div id="stage">
        <img id="liveimg" src="/admin/live-frame/{safe_id}?t=0">
      </div>
      <audio id="liveaudio" style="display:none"></audio>
      <button id="audiobtn">&#128266; Enable Live Audio</button>
      <button id="fsbtn">View Fullscreen</button>

      <script>
        const studentId = "{safe_id}";
        const img = document.getElementById('liveimg');
        const pill = document.getElementById('status-pill');
        const stage = document.getElementById('stage');
        const fsbtn = document.getElementById('fsbtn');
        const audiobtn = document.getElementById('audiobtn');
        const liveaudio = document.getElementById('liveaudio');

        let audioEnabled = false;
        let audioTimer = null;

        function refreshImage(){{
          img.src = `/admin/live-frame/${{encodeURIComponent(studentId)}}?t=${{Date.now()}}`;
        }}

        function playLatestAudioChunk(){{
          liveaudio.src = `/admin/live-audio/${{encodeURIComponent(studentId)}}?t=${{Date.now()}}`;
          liveaudio.play().catch(() => {{}});
        }}

        // Browsers block unmuted autoplay without a real click, so
        // live audio only starts once the admin explicitly clicks
        // this button (one-time, per page load).
        audiobtn.addEventListener('click', () => {{
          if (audioEnabled) return;
          audioEnabled = true;
          audiobtn.textContent = '🔊 Live Audio On';
          audiobtn.classList.add('on');
          playLatestAudioChunk();
          audioTimer = setInterval(playLatestAudioChunk, 2400);
        }});

        async function refreshStatus(){{
          try {{
            const res = await fetch('/admin/live-status');
            const sessions = await res.json();
            const mine = sessions.find(s => s.student_id === studentId);
            if (!mine) {{
              pill.textContent = 'Offline';
              pill.className = 'status-warning';
              return;
            }}
            if (mine.warning) {{
              pill.textContent = mine.warning_message || 'Warning';
              pill.className = 'status-warning';
            }} else {{
              pill.textContent = 'Normal — ' + (mine.student_name || studentId);
              pill.className = 'status-normal';
            }}
          }} catch(e) {{ console.error(e); }}
        }}

        fsbtn.addEventListener('click', () => {{
          if (stage.requestFullscreen) stage.requestFullscreen();
          else if (stage.webkitRequestFullscreen) stage.webkitRequestFullscreen();
        }});

        refreshImage();
        refreshStatus();
        setInterval(refreshImage, 1000);
        setInterval(refreshStatus, 2000);
      </script>
    </body>
    </html>
    """

    return html




@app.route("/admin/live-audio/<student_id>")
def admin_live_audio(student_id):

    if "admin_id" not in session:
        return redirect(url_for("admin_login"))

    safe_id = "".join(c for c in student_id if c.isalnum() or c in "-_")

    filepath = os.path.join(LIVE_FRAMES_FOLDER, f"{safe_id}_audio.webm")

    if not os.path.isfile(filepath):
        return "", 204

    response = send_from_directory(LIVE_FRAMES_FOLDER, f"{safe_id}_audio.webm")
    response.headers["Cache-Control"] = "no-store, no-cache, must-revalidate"
    return response


# ============================================================
# REMOTE VOICE BROADCAST — ADMIN SIGNALING PROXY
# ============================================================

def _student_signal_headers():
    return {
        "X-Voice-Signal-Token": VOICE_SIGNAL_TOKEN,
        "Content-Type": "application/json",
    }


# ============================================================
# ADMIN PROXY — CONTINUOUS LIVE VIDEO SIGNALING
# ============================================================
def _student_video_base_url(student_id):
    for sess in get_active_live_sessions():
        if str(sess.get("student_id", "")) == str(student_id):
            base = str(sess.get("student_signal_base_url", "")).strip().rstrip("/")
            if base:
                return base
            break
    return STUDENT_SIGNAL_BASE_URL.rstrip("/")


def _student_video_headers():
    return {"X-Video-Signal-Token": VOICE_SIGNAL_TOKEN, "Content-Type": "application/json"}


@app.route("/admin/video/offer", methods=["POST"])
def admin_video_offer():
    if "admin_id" not in session:
        return jsonify({"success": False, "error": "Admin login required"}), 401
    data = request.get_json(silent=True) or {}
    student_id = str(data.get("student_id", "")).strip()
    exam_id = str(data.get("exam_id", "")).strip()
    offer = data.get("offer")
    if not student_id or not exam_id or not isinstance(offer, dict):
        return jsonify({"success": False, "error": "student_id, exam_id and offer are required"}), 400
    try:
        r = requests.post(
            f"{_student_video_base_url(student_id)}/internal/video/offer",
            json={"student_id": student_id, "exam_id": exam_id, "offer": offer},
            headers=_student_video_headers(), timeout=8, verify=STUDENT_SIGNAL_VERIFY_SSL,
        )
        try: payload = r.json()
        except Exception: payload = {"success": False, "error": r.text[:500]}
        return jsonify(payload), r.status_code
    except Exception as e:
        print("[LIVE VIDEO] offer proxy error:", e)
        return jsonify({"success": False, "error": str(e)}), 502


@app.route("/admin/video/answer/<student_id>")
def admin_video_answer(student_id):
    if "admin_id" not in session:
        return jsonify({"success": False, "error": "Admin login required"}), 401
    safe_id = "".join(c for c in str(student_id) if c.isalnum() or c in "-_")
    try:
        r = requests.get(
            f"{_student_video_base_url(safe_id)}/internal/video/answer/{safe_id}",
            headers={"X-Video-Signal-Token": VOICE_SIGNAL_TOKEN}, timeout=8, verify=STUDENT_SIGNAL_VERIFY_SSL,
        )
        try: payload = r.json()
        except Exception: payload = {"success": False, "error": r.text[:500]}
        return jsonify(payload), r.status_code
    except Exception as e:
        print("[LIVE VIDEO] answer proxy error:", e)
        return jsonify({"success": False, "error": str(e)}), 502


@app.route("/admin/video/stop/<student_id>", methods=["POST"])
def admin_video_stop(student_id):
    if "admin_id" not in session:
        return jsonify({"success": False, "error": "Admin login required"}), 401
    safe_id = "".join(c for c in str(student_id) if c.isalnum() or c in "-_")
    try:
        r = requests.post(
            f"{_student_video_base_url(safe_id)}/internal/video/clear/{safe_id}",
            headers={"X-Video-Signal-Token": VOICE_SIGNAL_TOKEN}, timeout=8, verify=STUDENT_SIGNAL_VERIFY_SSL,
        )
        try: payload = r.json()
        except Exception: payload = {"success": False, "error": r.text[:500]}
        return jsonify(payload), r.status_code
    except Exception as e:
        print("[LIVE VIDEO] stop proxy error:", e)
        return jsonify({"success": False, "error": str(e)}), 502


@app.route("/admin/voice/offer", methods=["POST"])
def admin_voice_offer():
    """Forward an admin WebRTC offer to the student server."""
    if "admin_id" not in session:
        return jsonify({"success": False, "error": "Admin login required"}), 401

    data = request.get_json(silent=True) or {}
    student_id = str(data.get("student_id", "")).strip()
    exam_id = str(data.get("exam_id", "")).strip()
    offer = data.get("offer")

    if not student_id or not exam_id or not isinstance(offer, dict):
        return jsonify({"success": False, "error": "student_id, exam_id and offer are required"}), 400

    try:
        r = requests.post(
            # FIX: this used to always go to the single fixed
            # STUDENT_SIGNAL_BASE_URL (default 127.0.0.1:5000) no
            # matter which student it was for. On one computer that
            # accidentally worked; across multiple student computers
            # it meant admin's voice could only ever reach whichever
            # one machine happened to match that address — every
            # other student got nothing. Now uses the same per-student
            # self-reported address (from their live heartbeat) that
            # the video feed already relays through correctly.
            f"{_student_video_base_url(student_id)}/internal/voice/offer",
            json={"student_id": student_id, "exam_id": exam_id, "offer": offer},
            headers=_student_signal_headers(),
            timeout=8,
            verify=STUDENT_SIGNAL_VERIFY_SSL,
        )
        try:
            payload = r.json()
        except Exception:
            payload = {"success": False, "error": r.text[:500]}
        return jsonify(payload), r.status_code
    except Exception as e:
        print("[VOICE] Offer proxy error:", e)
        return jsonify({"success": False, "error": f"Student server unavailable: {e}"}), 502


@app.route("/admin/voice/answer/<student_id>")
def admin_voice_answer(student_id):
    """Fetch the student's WebRTC answer from the student server."""
    if "admin_id" not in session:
        return jsonify({"success": False, "error": "Admin login required"}), 401

    safe_id = "".join(c for c in str(student_id) if c.isalnum() or c in "-_")
    if not safe_id:
        return jsonify({"success": False, "error": "Invalid student id"}), 400

    try:
        r = requests.get(
            f"{_student_video_base_url(safe_id)}/internal/voice/answer/{safe_id}",
            headers={"X-Voice-Signal-Token": VOICE_SIGNAL_TOKEN},
            timeout=8,
            verify=STUDENT_SIGNAL_VERIFY_SSL,
        )
        try:
            payload = r.json()
        except Exception:
            payload = {"success": False, "error": r.text[:500]}
        return jsonify(payload), r.status_code
    except Exception as e:
        print("[VOICE] Answer proxy error:", e)
        return jsonify({"success": False, "error": f"Student server unavailable: {e}"}), 502


@app.route("/admin/voice/stop/<student_id>", methods=["POST"])
def admin_voice_stop(student_id):
    """Tell the student server to discard signaling state for one student."""
    if "admin_id" not in session:
        return jsonify({"success": False, "error": "Admin login required"}), 401

    safe_id = "".join(c for c in str(student_id) if c.isalnum() or c in "-_")
    try:
        r = requests.post(
            f"{_student_video_base_url(safe_id)}/internal/voice/clear/{safe_id}",
            headers=_student_signal_headers(),
            timeout=8,
            verify=STUDENT_SIGNAL_VERIFY_SSL,
        )
        try:
            payload = r.json()
        except Exception:
            payload = {"success": False, "error": r.text[:500]}
        return jsonify(payload), r.status_code
    except Exception as e:
        print("[VOICE] Stop proxy error:", e)
        return jsonify({"success": False, "error": f"Student server unavailable: {e}"}), 502


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
    /* FIX: on short pages (e.g. the landing page), <body> only grew
       as tall as its own content, so anything below/above that —
       down to the bottom of the browser window, and a thin strip
       above from margin-collapse with the first block inside it —
       showed the browser's plain white default instead of this
       background. min-height guarantees body always covers at least
       the full window; display:flow-root stops that top-margin leak;
       and html gets the same background as a belt-and-suspenders
       fallback for anywhere body still doesn't reach. */
    min-height: 100vh;
    margin: 0 !important;
    display: flow-root;
}
html {
    background: #0a0e1a !important;
    min-height: 100%;
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




@app.after_request
def inject_admin_ui(response):
    try:
        # Applied to every admin/teacher page (not a fixed whitelist),
        # so results pages, recordings, and live-monitoring pages get
        # the same attractive background too — previously only the
        # login/dashboard pages had it, so everything else stayed
        # plain black.
        if (
            request.method == "GET"
            and "text/html" in response.content_type
            and not response.is_streamed
        ):
            body = response.get_data(as_text=True)
            if "ai-dashboard-bg-applied" not in body:
                marker = "<!--ai-dashboard-bg-applied-->"
                if "</head>" in body:
                    body = body.replace("</head>", marker + DASHBOARD_BACKGROUND_CSS + "</head>")
                elif "<body" in body:
                    body = body.replace("<body", marker + DASHBOARD_BACKGROUND_CSS + "<body", 1)
                response.set_data(body)

        if (
            request.method == "GET"
            and request.path == "/dashboard"
            and "text/html" in response.content_type
            and not response.is_streamed
        ):
            body = response.get_data(as_text=True)
            if "ai-edit-exams-link" not in body and "</body>" in body:
                link = (
                    '<a id="ai-edit-exams-link" href="/teacher/exams/manage" '
                    'style="position:fixed;right:20px;bottom:76px;z-index:9999;padding:10px 14px;'
                    'background:#3b82f6;color:#fff;text-decoration:none;border-radius:7px;'
                    'font-family:Segoe UI,Arial,sans-serif;font-weight:700">✎ Edit / Manage Exams</a>'
                )
                body = body.replace("</body>", link + "</body>")
                response.set_data(body)

        if (
            request.method == "GET"
            and request.path == "/admin/dashboard"
            and "text/html" in response.content_type
            and not response.is_streamed
        ):
            body = response.get_data(as_text=True)
            if "ai-admin-quicklinks" not in body and "</body>" in body:
                links = (
                    '<div id="ai-admin-quicklinks" '
                    'style="position:fixed;right:20px;bottom:20px;z-index:9999;display:flex;gap:10px">'
                    '<a href="/admin/live" style="padding:10px 14px;background:#e0405c;color:#faf8f5;'
                    'text-decoration:none;border-radius:6px;font-family:Segoe UI,Arial,sans-serif;'
                    'font-weight:700">&#9679; Live Monitoring</a>'
                    '<a href="/admin/recordings" style="padding:10px 14px;background:#7c5cff;color:#fff;'
                    'text-decoration:none;border-radius:6px;font-family:Segoe UI,Arial,sans-serif;'
                    'font-weight:600">Exam Recordings</a>'
                    '</div>'
                )
                body = body.replace("</body>", links + "</body>")
                response.set_data(body)

    except Exception as e:
        print("UI injection error:", e)

    return response


if __name__ == "__main__":

    initialize_database()
    ensure_recording_column()
    ensure_exam_status_column()
    ensure_result_student_detail_columns()
    ensure_exam_timing_columns()
    ensure_exam_duration_column()
    ensure_violations_sheet()

    import socket
    try:
        hostname = socket.gethostname()
        local_ip = socket.gethostbyname(hostname)
    except Exception:
        local_ip = "your-computer-ip"

    print("=" * 60)
    print("ADMIN / TEACHER MANAGEMENT SYSTEM")
    print("On this computer:      https://127.0.0.1:5050")
    print(f"From other computers:  https://{local_ip}:5050")
    print("Remote microphone broadcast requires HTTPS.")
    print("For production, use a trusted HTTPS certificate/reverse proxy.")
    print("=" * 60)

    ssl_context = "adhoc"
    cert_file = os.environ.get("EXAM_SSL_CERT", "").strip()
    key_file = os.environ.get("EXAM_SSL_KEY", "").strip()
    if cert_file and key_file:
        ssl_context = (cert_file, key_file)

    app.run(
        host="0.0.0.0",
        port=5050,
        debug=False,
        use_reloader=False,
        # FIX: this server has to simultaneously handle every
        # student's live-monitoring sync traffic AND the admin's own
        # live-page polling. Without threaded=True it can only
        # process one request at a time, which — combined with the
        # sync volume — is the reason Live Monitoring was always
        # showing zero students (see the matching comment in
        # student_app.py next to LIVE_SYNC_MIN_INTERVAL_SECONDS).
        threaded=True,
        ssl_context=ssl_context
    )
