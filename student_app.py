from flask import Flask, render_template, request, redirect, url_for, session, flash, jsonify, send_file, send_from_directory
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
ADMIN_SYNC_BASE_URL=os.environ.get("EXAMGUARD_ADMIN_BASE_URL","https://192.168.1.24:5050").rstrip("/")
ADMIN_SYNC_TOKEN=os.environ.get("EXAMGUARD_RECORDING_SYNC_TOKEN","EXAMGUARD-RECORDING-2026-LOCAL").strip()
ADMIN_SYNC_VERIFY_SSL=os.environ.get("EXAMGUARD_ADMIN_VERIFY_SSL","false").strip().lower() in ("1","true","yes","on")
LIVE_MONITOR_BUILD="V3-DIRECT-PULL"
LIVE_SYNC_TOKEN=os.environ.get("EXAMGUARD_LIVE_SYNC_TOKEN","EXAMGUARD-LIVE-2026-LOCAL").strip()
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
MAR_THRESHOLD = 0.60
# FIX: these were set to 5 degrees / 0.05-0.06 gaze ratio, which is
# tighter than normal, involuntary head and eye movement — a student
# looking straight at the screen would still trip "Please look
# straight" almost constantly. Widened to tolerate natural movement
# while still catching someone who is genuinely turned away.
YAW_THRESHOLD = 15
PITCH_THRESHOLD = 15
ROLL_THRESHOLD = 12
GAZE_THRESHOLD_H = 0.12
GAZE_THRESHOLD_V = 0.14
FRAME_CHECK = 4
# FIX: gaze warnings used to fire on a single off-center frame
# (gaze_off_frames >= 1), unlike every other warning here which
# requires FRAME_CHECK consecutive bad frames. One noisy frame from
# pupil-tracking jitter was enough to trigger a false warning, so
# gaze now needs the same sustained-frames check as the rest.
GAZE_FRAME_CHECK = FRAME_CHECK
# FIX: "no face detected" used to fire as a warning on the very
# first frame with no landmarks, with no debounce at all — unlike
# every other warning here. Right when an exam starts, the webcam
# is often still auto-focusing/adjusting exposure, or the very first
# frame or two just misses a detection by chance; at one warning per
# monitor poll (every 1.5s) and a 3-strike limit, that alone was
# enough to auto-submit a student's exam within 4-5 seconds of them
# starting it, with no actual malpractice. Requiring a few
# consecutive misses before it counts as a real warning absorbs that
# startup jitter while still catching someone who is genuinely out
# of frame.
NO_FACE_FRAME_CHECK = FRAME_CHECK

# Require transient-prone head pose / multiple-face / phone detections to
# persist for several AI frames before they become a malpractice warning.
# This prevents one noisy MediaPipe frame from becoming a strike.
HEAD_POSE_FRAME_CHECK = 4
MULTIPLE_FACE_FRAME_CHECK = 2
PHONE_FRAME_CHECK = 2

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
            max_num_faces=2,
            refine_landmarks=True,
            min_detection_confidence=0.5,
            min_tracking_confidence=0.5,
        ),
        "ear_history": deque(maxlen=20),
        "blink_times": deque(maxlen=20),
        "blink_count": 0,
        "total_frames": 0,
        "eye_closed_frames": 0,
        "gaze_off_frames": 0,
        "mouth_open_frames": 0,
        "no_face_frames": 0,
        "yaw_bad_frames": 0,
        "pitch_bad_frames": 0,
        "roll_bad_frames": 0,
        "multiple_face_frames": 0,
        "phone_bad_frames": 0,
        "last_blink_time": 0.0,
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
_phone_check_counter = 0
# FIX: was 2 (skipped every other frame) + 0.45 threshold. Reports of
# phones not being detected are consistent with this being too
# conservative — efficientdet_lite0 is a small/fast model that is
# already lower-accuracy than a full-size detector, so skipping half
# the frames on top of a fairly high confidence threshold meant a
# phone had to be held clearly in frame for a while before it was
# ever even checked, let alone cleared 0.45 confidence. Checking every
# frame and lowering the threshold trades a bit of CPU/more sensitivity
# for meaningfully better catch-rate; PHONE_SCORE_THRESHOLD can be
# tuned back up if this now over-triggers on false positives.
PHONE_CHECK_EVERY_N_FRAMES = 3  # check every third AI frame
PHONE_SCORE_THRESHOLD = 0.35  # balanced sensitivity to reduce false positives

try:

    from mediapipe.tasks.python import vision as _mp_vision
    from mediapipe.tasks.python.core.base_options import BaseOptions as _MPBaseOptions

    OBJECT_MODEL_PATH = str(Path(BASE_DIR, "efficientdet_lite0.tflite").resolve()).replace("\\", "/")

    if os.path.exists(OBJECT_MODEL_PATH):

        _object_detector_options = _mp_vision.ObjectDetectorOptions(
            base_options=_MPBaseOptions(model_asset_path=OBJECT_MODEL_PATH),
            running_mode=_mp_vision.RunningMode.IMAGE,
            score_threshold=PHONE_SCORE_THRESHOLD,
            max_results=10
        )

        _object_detector = _mp_vision.ObjectDetector.create_from_options(_object_detector_options)
        PHONE_DETECTION_AVAILABLE = True
        print("Mobile phone detection: ENABLED (model found)")

    else:
        print(
            "Mobile phone detection: DISABLED — model file not found at "
            + OBJECT_MODEL_PATH
            + ". Download efficientdet_lite0.tflite and place it in the same "
            "folder as this script to enable it. Everything else runs normally."
        )

except Exception as _phone_setup_error:

    print(
        "Mobile phone detection: DISABLED — setup error:",
        str(_phone_setup_error),
        "| Everything else runs normally without this feature."
    )


def detect_phone_in_frame(frame):
    """Lightweight optional phone detector. It is called only after one face
    has been found and only every few AI frames, so it cannot overwhelm the
    student server or falsely classify a no-face frame as a phone warning."""
    global _phone_check_counter
    if not PHONE_DETECTION_AVAILABLE:
        return False
    _phone_check_counter += 1
    if _phone_check_counter % PHONE_CHECK_EVERY_N_FRAMES != 0:
        return False
    try:
        import mediapipe as _mp_full
        rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
        image = _mp_full.Image(image_format=_mp_full.ImageFormat.SRGB, data=rgb)
        result = _object_detector.detect(image)
        for detection in result.detections:
            for category in detection.categories:
                name = (category.category_name or '').strip().lower()
                if name in {'cell phone', 'mobile phone', 'phone'} and category.score >= PHONE_SCORE_THRESHOLD:
                    print(f"Phone detected: category={name}, score={category.score:.2f}")
                    return True
        return False
    except Exception as exc:
        print('Phone detection frame error (ignored):', exc)
        return False

def analyze_face_frame(frame, monitor_key):

    state = _get_monitor_state(monitor_key)

    with state["lock"]:

        height, width = frame.shape[:2]

        phone_detected = False

        rgb = cv2.cvtColor(
            frame,
            cv2.COLOR_BGR2RGB
        )


        results = state["face_mesh"].process(rgb)


        state["total_frames"] += 1


        # =====================================================
        # NO FACE
        # =====================================================

        if not results.multi_face_landmarks:

            state["no_face_frames"] += 1
            no_face_confirmed = state["no_face_frames"] >= NO_FACE_FRAME_CHECK

            state["latest_stats"] = {

                "ear": 0,

                "mar": 0,

                "closure": 0,

                "blink_rate": 0,

                "yaw": 0,

                "pitch": 0,

                "roll": 0,

                "face_count": 0,

                "status": "No Face",

                "eyes": "Unknown",

                "mouth": "Unknown",

                "looking": "Unknown",

                "head_pose": "Unknown",

                "eye_gaze": "Unknown",

                "gaze_ratio": 0.5,

                "warning": no_face_confirmed,

                "warning_message": (
                    (
                        "Mobile phone detected. Please remove it."
                        if phone_detected else
                        "Face not detected. Please look at the camera."
                    )
                    if no_face_confirmed else ""
                )
            }

            return state["latest_stats"]


        state["no_face_frames"] = 0
        state["multiple_face_frames"] = 0

        face_count = len(
            results.multi_face_landmarks
        )

        if face_count == 1 and PHONE_DETECTION_AVAILABLE:
            phone_detected = detect_phone_in_frame(frame)
        if phone_detected:
            state["phone_bad_frames"] += 1
        else:
            state["phone_bad_frames"] = 0
        phone_confirmed = state["phone_bad_frames"] >= PHONE_FRAME_CHECK

        # =====================================================
        # MULTIPLE FACES
        # =====================================================

        if face_count > 1:

            state["multiple_face_frames"] += 1
            state["yaw_bad_frames"] = 0
            state["pitch_bad_frames"] = 0
            state["roll_bad_frames"] = 0

            multiple_faces_confirmed = (
                state["multiple_face_frames"] >= MULTIPLE_FACE_FRAME_CHECK
            )

            state["latest_stats"]["face_count"] = face_count
            state["latest_stats"]["status"] = "Multiple Faces"
            state["latest_stats"]["warning"] = multiple_faces_confirmed
            state["latest_stats"]["warning_message"] = (
                "Other person detected. Only the student should be visible."
                if multiple_faces_confirmed else ""
            )

            return state["latest_stats"]


        # =====================================================
        # SINGLE FACE
        # =====================================================

        face_landmarks = (
            results.multi_face_landmarks[0]
            .landmark
        )

        # =====================================================
        # EAR
        # =====================================================

        left_ear = calculate_ear(
            face_landmarks,
            LEFT_EYE,
            width,
            height
        )


        right_ear = calculate_ear(
            face_landmarks,
            RIGHT_EYE,
            width,
            height
        )


        ear = (
            left_ear + right_ear
        ) / 2.0


        state["ear_history"].append(ear)


        # =====================================================
        # EYE STATUS
        # =====================================================

        eyes_closed = (
            ear < EAR_THRESHOLD
        )


        if eyes_closed:

            state["eye_closed_frames"] += 1

            eyes_status = "Closed"

        else:

            state["eye_closed_frames"] = 0

            eyes_status = "Open"


        # =====================================================
        # BLINK DETECTION
        # =====================================================

        ear_history = state["ear_history"]

        if len(ear_history) >= 2:

            previous_ear = ear_history[-2]


            if (
                previous_ear < EAR_THRESHOLD
                and ear >= EAR_THRESHOLD
            ):

                current_time = time.time()


                # Avoid duplicate blink counting
                if current_time - state["last_blink_time"] > 0.15:

                    state["blink_count"] += 1

                    state["blink_times"].append(
                        current_time
                    )

                    state["last_blink_time"] = current_time


        # =====================================================
        # BLINK RATE
        # =====================================================

        current_time = time.time()

        blink_times = state["blink_times"]

        while (
            blink_times
            and current_time - blink_times[0] > 60
        ):

            blink_times.popleft()


        blink_rate = len(
            blink_times
        )


        # =====================================================
        # EYE CLOSURE %
        # =====================================================

        if state["total_frames"] > 0:

            closure_percentage = (
                state["eye_closed_frames"]
                / state["total_frames"]
            ) * 100

        else:

            closure_percentage = 0


        # =====================================================
        # MAR
        # =====================================================

        mar = calculate_mar(
            face_landmarks,
            width,
            height
        )


        if mar > MAR_THRESHOLD:

            mouth_status = "Open"

            state["mouth_open_frames"] += 1

        else:

            mouth_status = "Normal"

            state["mouth_open_frames"] = 0


        # =====================================================
        # EYE GAZE (where the pupils are pointing — independent
        # of head rotation, using the iris landmarks unlocked by
        # refine_landmarks=True). Checks BOTH axes: left/right AND
        # up/down, not just horizontal.
        # =====================================================

        left_gaze_ratio_h = calculate_gaze_ratio(
            face_landmarks,
            (LEFT_EYE[0], LEFT_EYE[3]),
            LEFT_IRIS_CENTER,
            width
        )

        right_gaze_ratio_h = calculate_gaze_ratio(
            face_landmarks,
            (RIGHT_EYE[0], RIGHT_EYE[3]),
            RIGHT_IRIS_CENTER,
            width
        )

        gaze_ratio_h = (left_gaze_ratio_h + right_gaze_ratio_h) / 2.0

        left_gaze_ratio_v = calculate_vertical_gaze_ratio(
            face_landmarks,
            LEFT_EYE_TOP,
            LEFT_EYE_BOTTOM,
            LEFT_IRIS_CENTER,
            height
        )

        right_gaze_ratio_v = calculate_vertical_gaze_ratio(
            face_landmarks,
            RIGHT_EYE_TOP,
            RIGHT_EYE_BOTTOM,
            RIGHT_IRIS_CENTER,
            height
        )

        gaze_ratio_v = (left_gaze_ratio_v + right_gaze_ratio_v) / 2.0
        # Combined gaze value used by the stats payload.
        gaze_ratio = (gaze_ratio_h + gaze_ratio_v) / 2.0

        horizontal_label = None

        if gaze_ratio_h < (0.5 - GAZE_THRESHOLD_H):
            horizontal_label = "Left"
        elif gaze_ratio_h > (0.5 + GAZE_THRESHOLD_H):
            horizontal_label = "Right"

        vertical_label = None

        if gaze_ratio_v < (0.5 - GAZE_THRESHOLD_V):
            vertical_label = "Up"
        elif gaze_ratio_v > (0.5 + GAZE_THRESHOLD_V):
            vertical_label = "Down"

        if vertical_label and horizontal_label:
            eye_gaze = f"Eyes {vertical_label}-{horizontal_label}"
        elif vertical_label:
            eye_gaze = f"Eyes {vertical_label}"
        elif horizontal_label:
            eye_gaze = f"Eyes {horizontal_label}"
        else:
            eye_gaze = "Eyes Center"


        gaze_off_center = (eye_gaze != "Eyes Center")

        if gaze_off_center and not eyes_closed:

            state["gaze_off_frames"] += 1

        else:

            state["gaze_off_frames"] = 0


        # =====================================================
        # HEAD POSE
        # =====================================================


        pitch, yaw, roll = calculate_head_pose(face_landmarks,width,height)

        # =====================================================
        # LOOKING DIRECTION
        # =====================================================

        if yaw >= YAW_THRESHOLD:

            looking = "Looking Right"

        elif yaw <= -YAW_THRESHOLD:

            looking = "Looking Left"

        else:

            looking = "Looking Center"


        # =====================================================
        # HEAD TILT
        # =====================================================

        if abs(roll) >= ROLL_THRESHOLD:
            head_pose = "Head Tilted"
        elif pitch >= PITCH_THRESHOLD:
            head_pose = "Looking Down"
        elif pitch <= -PITCH_THRESHOLD:
            head_pose = "Looking Up"
        else:
            head_pose = "Normal"

        # Debounce head-pose warnings. A student can naturally cross a
        # threshold for one or two frames while reading or moving.
        state["yaw_bad_frames"] = state["yaw_bad_frames"] + 1 if abs(yaw) >= YAW_THRESHOLD else 0
        state["pitch_bad_frames"] = state["pitch_bad_frames"] + 1 if abs(pitch) >= PITCH_THRESHOLD else 0
        state["roll_bad_frames"] = state["roll_bad_frames"] + 1 if abs(roll) >= ROLL_THRESHOLD else 0

        yaw_confirmed = state["yaw_bad_frames"] >= HEAD_POSE_FRAME_CHECK
        pitch_confirmed = state["pitch_bad_frames"] >= HEAD_POSE_FRAME_CHECK
        roll_confirmed = state["roll_bad_frames"] >= HEAD_POSE_FRAME_CHECK

        # =====================================================
        # WARNING LOGIC
        # =====================================================

        warning = False

        warning_message = ""


        if phone_confirmed:

            warning = True

            warning_message = (
                "Mobile phone detected. Please remove it."
            )


        elif yaw_confirmed:

            warning = True

            warning_message = (
                "Please look straight at the camera."
            )


        elif pitch_confirmed:

            warning = True

            warning_message = (
                "Please keep your face straight."
            )


        elif roll_confirmed:

            warning = True

            warning_message = (
                "Please keep your head straight."
            )


        elif state["eye_closed_frames"] >= FRAME_CHECK:

            warning = True

            warning_message = (
                "Eyes closed for too long. "
                "Please stay attentive."
            )


        elif state["gaze_off_frames"] >= GAZE_FRAME_CHECK:

            warning = True

            warning_message = (
                f"Eyes are not looking at the screen ({eye_gaze}). "
                "Please look straight at your screen."
            )


        # FIX: this used to fire on state["mouth_open_frames"] >= 1 —
        # a single frame of a slightly-open mouth (yawning, adjusting
        # a mask, a brief word to a proctor) instantly counted as a
        # warning, with no debounce at all unlike every other check
        # here. Now requires the same sustained FRAME_CHECK run as
        # eyes/gaze/head-pose before it's treated as real talking.
        elif state["mouth_open_frames"] >= FRAME_CHECK:

            warning = True

            warning_message = (
                "Mouth movement detected. "
                "Please avoid talking during the examination."
            )


        # =====================================================
        # STATUS
        # =====================================================

        if warning:

            status = "Warning"

        else:

            status = "Normal"


        state["latest_stats"] = {

            "ear": round(ear, 3),

            "mar": round(mar, 3),

            "closure": round(
                closure_percentage,
                2
            ),

            "blink_rate": blink_rate,

            "blink_count": state["blink_count"],

            "yaw": round(yaw, 2),

            "pitch": round(pitch, 2),

            "roll": round(roll, 2),

            "face_count": face_count,

            "status": status,

            "eyes": eyes_status,

            "mouth": mouth_status,

            "looking": looking,

            "head_pose": head_pose,

            "eye_gaze": eye_gaze,

            "gaze_ratio": round(gaze_ratio, 3),

            "warning": warning,

            "warning_message": warning_message
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
            datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
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




@app.route("/student/dashboard")
@student_login_required
def student_dashboard():

    workbook = load_database()

    sheet = workbook["Exams"]

    subjects = {}

    for row in sheet.iter_rows(min_row=2, values_only=True):

        exam_id = row[0]
        subject_name = row[3]
        subject_code = row[4]
        teacher_name = row[2]

        if exam_id not in subjects:

            subjects[exam_id] = {
                "exam_id": exam_id,
                "subject_name": subject_name,
                "subject_code": subject_code,
                "teacher_name": teacher_name
            }

    workbook.close()

    subject_list = list(subjects.values())

    return render_template(
        "student_dashboard.html",
        subjects=subject_list
    )


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
            r=requests.post(f"{ADMIN_SYNC_BASE_URL}/internal/sync/recording",headers={"X-ExamGuard-Sync-Token":ADMIN_SYNC_TOKEN},data={"exam_id":str(exam_id),"student_id":str(student_id),"filename":_safe_admin_filename(filename)},files={"recording":(filename,fh,"video/webm")},timeout=(8,180),verify=ADMIN_SYNC_VERIFY_SSL)
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
                if _post_recording_chunk_to_admin(path, exam_id, student_id, filename, token, seq):
                    ok = True
                    break
                time.sleep(min(8, attempt))
            if not ok:
                print(f"[SYNC] Recording chunk remains queued: {token}:{seq}")
        finally:
            RECORDING_CHUNK_SYNC_QUEUE.task_done()


def _start_recording_chunk_sync_worker():
    global RECORDING_CHUNK_SYNC_THREAD_STARTED
    with RECORDING_CHUNK_SYNC_START_LOCK:
        if not RECORDING_CHUNK_SYNC_THREAD_STARTED:
            for i in range(3):
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


def _queue_recording_for_admin(path,exam_id,student_id,filename,try_immediately=True):
    if not path or not os.path.isfile(path): return
    filename=_safe_admin_filename(filename); marker=os.path.join(ADMIN_SYNC_FOLDER,filename+".json")
    try:
        with open(marker,"w",encoding="utf-8") as fh: json.dump({"path":path,"exam_id":str(exam_id),"student_id":str(student_id),"filename":filename},fh)
    except Exception as e: print("[SYNC] recording queue:",e)

    # FIX: previously this only ever synced to admin on a background
    # thread with the first attempt starting after some delay — the
    # video could sit unsynced for a while, and if the student's
    # computer/app was shut down soon after they saw their results,
    # it might never get there at all. Since the request that calls
    # this (finalize) is a good moment to actually wait a few seconds
    # for it, try once, right now, before falling back to the same
    # durable background retry queue as before for resilience against
    # a slow/flaky connection.
    if try_immediately and _post_recording_to_admin(path,exam_id,student_id,filename):
        try: os.remove(marker)
        except OSError: pass
        print("[SYNC] Recording synced to admin immediately:",filename)
        return

    def worker():
        for attempt in range(1,13):
            if _post_recording_to_admin(path,exam_id,student_id,filename):
                try: os.remove(marker)
                except OSError: pass
                print("[SYNC] Recording synced to admin:",filename); return
            time.sleep(min(10,attempt*2))
        print("[SYNC] Recording remains queued:",filename)
    threading.Thread(target=worker,daemon=True).start()

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
LIVE_FRAME_SYNC_INTERVAL = 0.8

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
                },
                files={"frame":("live.jpg",fh,"image/jpeg")},
                timeout=(2,4),
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
            },
            timeout=(1.5,2.5),
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
                f"{ADMIN_SYNC_BASE_URL}/internal/sync/live-audio",
                headers={"X-ExamGuard-Sync-Token":LIVE_SYNC_TOKEN},
                data={"student_id":str(student_id)},
                files={"audio":("chunk.webm",fh,"audio/webm")},
                timeout=(2,6),
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

    submitted_at = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

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
    # DISPLAY RESULT
    # =========================================================

    return render_template(

        "student_result.html",

        result_id=result_id,

        exam_id=exam_id,

        subject_name=subject_name,

        subject_code=subject_code,

        questions=result_questions,

        total_questions=total_questions,

        correct_count=correct_count,

        wrong_count=wrong_count,

        unattempted_count=unattempted_count,

        percentage=percentage,

        exam_status=exam_status

    )



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
            meta["updated_at"] = datetime.now().isoformat(timespec="seconds")
            _save_recording_meta(part_dir, meta)
            try:
                os.remove(part_path)
            except OSError:
                pass
        return next_seq, partial_path


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
                "created_at": datetime.now().isoformat(timespec="seconds"),
                "updated_at": datetime.now().isoformat(timespec="seconds"),
            }
            _save_recording_meta(part_dir, meta)
        elif (str(meta.get("student_id", "")) != str(session.get("student_id", ""))
              or str(meta.get("exam_id", "")) != str(exam_id)):
            return jsonify({"success": False, "error": "Recording token does not match this exam"}), 403

        part_path = os.path.join(part_dir, f"{seq:08d}.part")
        if not os.path.isfile(part_path):
            with open(part_path, "wb") as out_file:
                shutil.copyfileobj(video.stream, out_file, length=1024 * 1024)
        meta["updated_at"] = datetime.now().isoformat(timespec="seconds")
        _save_recording_meta(part_dir, meta)

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
        _queue_recording_for_admin(final_path, exam_id, session.get("student_id", ""), filename)
        return jsonify({"success":True,"filename":filename})
    except Exception as e:
        print("Recording Finalize Error:",str(e))
        return jsonify({"success":False,"error":str(e)}),500




def _background_finalize_recording(exam_id, student_id, token, expected_last_seq, wait_seconds=45):
    """Finalize a continuously uploaded recording after result submission.

    This runs outside the student's submit request so the result page is not
    held up by recording assembly/upload timing.  It waits briefly for the
    final MediaRecorder chunk(s), then assembles the already-uploaded parts.
    """
    try:
        part_dir = os.path.join(RECORDINGS_FOLDER, ".examguard_parts", token)
        deadline = time.time() + max(1, int(wait_seconds))
        while time.time() < deadline:
            meta = _load_recording_meta(part_dir) if os.path.isdir(part_dir) else None
            if meta and str(meta.get("student_id", "")) == str(student_id) and str(meta.get("exam_id", "")) == str(exam_id):
                next_seq, partial = _assemble_ready_recording_parts(part_dir, meta)
                if expected_last_seq is None or next_seq > expected_last_seq:
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
                        # FIX: no longer also signals the admin to
                        # reconstruct its own copy from individually
                        # pushed chunks — that pipeline is gone (see
                        # upload_exam_recording_chunk). This verified
                        # local file is the only source pushed to admin.
                        _queue_recording_for_admin(final_path, exam_id, student_id, filename)
                        return True
            time.sleep(0.25)
        print("Background recording finalize timed out:", token)
    except Exception as e:
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
        temp_path = frame_path + ".uploading"
        if not cv2.imwrite(temp_path, frame, [cv2.IMWRITE_JPEG_QUALITY, 55]):
            raise IOError("Could not encode live JPEG")

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
            "student_signal_base_url": f"https://{_local_lan_ip()}:5000"
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
            "student_signal_base_url": f"https://{_local_lan_ip()}:5000",
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


@app.route("/student/exam/keyboard-unlock", methods=["POST"])
@student_login_required
def keyboard_unlock():
    """Validate the teacher unlock password without exposing it to the browser."""
    data = request.get_json(silent=True) or {}
    exam_id = str(data.get("exam_id", "")).strip()
    candidate = str(data.get("password", ""))

    current_exam = str(session.get("current_exam_id", ""))
    result_exam = str(session.get("result_lock_exam_id", ""))
    if not exam_id or exam_id not in (current_exam, result_exam):
        return jsonify({"success": False, "unlocked": False}), 403

    # Only the server knows the real password.
    unlocked = bool(KEYBOARD_UNLOCK_PASSWORD and KEYBOARD_UNLOCK_PASSWORD != ""
                    and candidate == KEYBOARD_UNLOCK_PASSWORD)
    if unlocked and result_exam and exam_id == result_exam:
        session.pop("result_lock_exam_id", None)
    return jsonify({"success": True, "unlocked": unlocked})


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

    if "Results" in results_workbook.sheetnames:

        results_sheet = results_workbook["Results"]

        for row in results_sheet.iter_rows(min_row=2, values_only=True):

            if row[1] == student_id and row[3] == exam_id:

                exam_status = row[12] if len(row) > 12 and row[12] else "Completed"

                results_workbook.close()

                if exam_status != "Completed":
                    flash(
                        f"Your access to this exam was ended due to a policy violation ({exam_status}). "
                        "You cannot re-attempt it.",
                        "error"
                    )
                else:
                    flash(
                        "You have already completed this exam and cannot retake it.",
                        "error"
                    )

                return redirect(url_for("student_dashboard"))

    results_workbook.close()

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
    now = datetime.now()

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

        for fmt in ("%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M"):
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
  async function sendRecordingPart(blob,seq,attempts=2){
    if(!blob||!blob.size)return false;
    for(let a=1;a<=attempts;a++){
      try{
        const fd=new FormData();fd.append('video',blob,`chunk_${seq}.webm`);
        const r=await fetchWithTimeout(`/student/exam/${encodeURIComponent(examId)}/upload-recording-chunk`,{method:'POST',body:fd,credentials:'same-origin',headers:{'X-Recording-Token':recordingToken,'X-Recording-Seq':String(seq)}},2500);
        const d=await r.json().catch(()=>({}));
        if(r.ok&&d.success){if(d.filename)uploadedFile=d.filename;recordingBlobStore.delete(Number(seq));return true;}
      }catch(e){console.warn('Recording upload',seq,a,e);}
      await new Promise(r=>setTimeout(r,Math.min(800,a*180)));
    }
    return false;
  }
  function queueRecordingPart(blob){
    const seq=recordingSeq++; recordingBlobStore.set(seq,blob);
    const task=sendRecordingPart(blob,seq); pendingRecordingUploads.set(seq,task); task.finally(()=>pendingRecordingUploads.delete(seq));
  }
  async function waitForRecordingUploads(ms=3000){
    const end=Date.now()+ms; while(pendingRecordingUploads.size&&Date.now()<end){await Promise.race([Promise.allSettled(Array.from(pendingRecordingUploads.values())),new Promise(r=>setTimeout(r,150))]);}
  }
  async function retryMissing(seq){
    const blob=recordingBlobStore.get(Number(seq)); if(!blob)return;
    if(pendingRecordingUploads.has(Number(seq)))return;
    const task=sendRecordingPart(blob,Number(seq),4); pendingRecordingUploads.set(Number(seq),task); task.finally(()=>pendingRecordingUploads.delete(Number(seq)));
    return task;
  }
  async function finalizeRecording(){
    if(!recordingToken||recordingSeq===0)return '';
    // Give the final MediaRecorder chunk a moment to finish uploading, then
    // actively ask the server to assemble the complete recording. This is the
    // primary path; the server-side background finalizer remains the fallback.
    await waitForRecordingUploads(1800);
    const expected=recordingSeq-1;
    for(let attempt=1;attempt<=3;attempt++){
      const fd=new FormData();fd.append('recording_token',recordingToken);fd.append('expected_last_seq',String(expected));
      try{
        const r=await fetchWithTimeout(`/student/exam/${encodeURIComponent(examId)}/finalize-recording`,{method:'POST',body:fd,credentials:'same-origin'},2600);
        const d=await r.json().catch(()=>({}));
        if(r.ok&&d.success){uploadedFile=d.filename||uploadedFile||'';return uploadedFile;}
        if(d.retry&&Array.isArray(d.missing_sequences)){
          const missing=d.missing_sequences.slice(0,80);
          await Promise.all(missing.map(retryMissing)); await waitForRecordingUploads(900); continue;
        }
      }catch(e){console.warn('Recording finalize retry',attempt,e);}
      await new Promise(r=>setTimeout(r,300));
    }
    throw new Error('Recording finalization failed');
  }
  async function uploadCompleteRecording(){
    if(!chunks.length)return '';
    const mime = (recorder && recorder.mimeType) || (chunks[0] && chunks[0].type) || 'video/webm';
    const completeBlob = new Blob(chunks, {type:mime});
    if(!completeBlob.size)return '';
    const fd = new FormData();
    fd.append('video', completeBlob, 'exam_recording.webm');
    if(recordingToken) fd.append('recording_token', recordingToken);

    // This is the primary recording path. It writes one complete WebM file on
    // the Student server, avoiding any dependency on the rolling chunk order.
    for(let attempt=1; attempt<=3; attempt++){
      try{
        const r = await fetchWithTimeout(
          `/student/exam/${encodeURIComponent(examId)}/upload-recording`,
          {method:'POST', body:fd, credentials:'same-origin'},
          180000
        );
        const d = await r.json().catch(()=>({}));
        if(r.ok && d.success && d.filename){
          uploadedFile = d.filename;
          return uploadedFile;
        }
        console.warn('Complete recording upload rejected:', d);
      }catch(e){
        console.warn('Complete recording upload attempt', attempt, e);
      }
      await new Promise(r=>setTimeout(r, 700 * attempt));
    }
    return '';
  }

  async function stopAndSubmit(form){
    if(submitting)return; submitting=true;
    const hidden=addHiddenField(form,'recording_file');
    const tokenInput=addHiddenField(form,'recording_token');
    const seqInput=addHiddenField(form,'recording_expected_last_seq');
    if(window.__aiStopMonitoring)window.__aiStopMonitoring(); if(window.__aiStopAudioMonitoring)window.__aiStopAudioMonitoring(); if(window.__aiStopAdminVoice)window.__aiStopAdminVoice(); if(window.__aiStopLiveVideo)window.__aiStopLiveVideo();

    // Stop MediaRecorder first so its final dataavailable event is included in
    // `chunks`. Then upload the complete recording as ONE durable WebM file.
    // The older rolling-chunk pipeline remains below as a fallback only.
    try{
      if(recorder&&recorder.state!=='inactive')await new Promise(resolve=>{recorder.addEventListener('stop',resolve,{once:true});recorder.stop();});
    }catch(e){console.error('Recorder stop failed:',e);}

    status('Saving recording...');
    // Recording chunks have been uploading continuously during the exam.
    // Do not send a second giant Blob here; that was the source of the
    // upload-time failures and unnecessary delay. Give in-flight chunks a
    // short window, then finalize the already-transferred sequence.
    try{
      await Promise.race([
        (async()=>{ await waitForRecordingUploads(4500); if(recordingToken) await finalizeRecording(); })(),
        new Promise(resolve=>setTimeout(resolve,6000))
      ]);
    }catch(e){console.warn('Recording finalize deferred to background:',e);}

    hidden.value=uploadedFile||'';
    tokenInput.value=recordingToken||'';
    seqInput.value=String(Math.max(0, recordingSeq - 1));
    if(stream)stream.getTracks().forEach(t=>t.stop());
    status(uploadedFile ? 'Recording saved. Submitting exam...' : 'Submitting exam...');
    nativeSubmit.call(form);
  }

  // ===================== AI FACE / EYE / HEAD MONITORING =====================
  // Sends a webcam frame to the server every 1.5s for AI analysis.
  // Live camera display is handled independently by startLiveFrameLoop()
  // so the admin preview is not blocked by MediaPipe.
  let monitorTimer = null;
  let monitorInFlight = false;

  function startMonitoringLoop(){
    monitorTimer = setInterval(async () => {
      if (submitting || !video.videoWidth || monitorInFlight) return;
      monitorInFlight = true;

      try {
        ctx.drawImage(video, 0, 0, canvas.width, canvas.height);
        const imageData = canvas.toDataURL('image/jpeg', 0.6);

        const res = await fetch('/student/exam/monitor', {
          method: 'POST',
          headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({image: imageData, exam_id: examId})
        });
        const data = await res.json();
        if (data.success) updateStats(data.stats);
      } catch (e) {
        console.error('Monitoring error:', e);
      } finally {
        monitorInFlight = false;
      }
    }, 1500);
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

  function updateStats(stats){
    const wasActive = faceWarningActive;
    faceWarningActive = !!stats.warning;
    faceWarningMsg = stats.warning_message || '';
    if (faceWarningActive && !wasActive) faceWarningSince = Date.now();
    refreshWarningUI();

    if (stats.warning && window.__aiRegisterWarning) {
      const msg = stats.warning_message || 'Attention warning detected';
      let type = 'face_warning';
      if (/phone/i.test(msg)) type = 'phone_warning';
      else if (/Movement detected/i.test(msg)) type = 'movement_warning';
      else if (/look straight/i.test(msg)) type = 'head_direction_warning';
      else if (/face straight/i.test(msg)) type = 'head_pitch_warning';
      else if (/head straight|tilt/i.test(msg)) type = 'head_roll_warning';
      else if (/Eyes closed/i.test(msg)) type = 'eyes_closed_warning';
      else if (/Eyes are not looking/i.test(msg)) type = 'gaze_warning';
      else if (/Mouth movement/i.test(msg)) type = 'mouth_warning';
      else if (/Multiple faces|Other person/i.test(msg)) type = 'multiple_face_warning';
      else if (/Face not detected/i.test(msg)) type = 'no_face_warning';
      window.__aiRegisterWarning(type, msg);
    } else if (window.__aiClearWarningType) {
      // The condition is clear again, so a future separate occurrence
      // of the same type is allowed to count as a new warning.
      const warningTypes = [
        'phone_warning','head_direction_warning','head_pitch_warning',
        'head_roll_warning','eyes_closed_warning','gaze_warning',
        'mouth_warning','multiple_face_warning','no_face_warning',
        'face_warning'
      ];
      warningTypes.forEach(window.__aiClearWarningType);
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
      document.addEventListener('click', tryResume);
      document.addEventListener('keydown', tryResume);
      window.__aiResumeAudioContext = tryResume;

      let calibration = [];
      let baseline = 0.006;
      let consecutive = 0;
      let lastWarningAt = 0;
      const calibrationEnd = Date.now() + 4000;
      const ABSOLUTE = 0.024;
      const REQUIRED = 5;     // 5 x 250 ms = 1.25 s sustained
      const COOLDOWN = 10000; // sustained audio must stop before another warning

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

        if (Date.now() < calibrationEnd) {
          calibration.push(level);
          calibration = calibration.slice(-20);
          if (calibration.length >= 5) {
            const sorted = calibration.slice().sort((a,b)=>a-b);
            baseline = sorted[Math.floor(sorted.length/2)] || baseline;
          }
          consecutive = 0;
          return;
        }

        // Track only the quiet baseline; never let loud audio raise the baseline.
        if (level < Math.max(0.032, baseline * 1.25)) {
          baseline = baseline * 0.98 + level * 0.02;
        }

        const threshold = Math.max(ABSOLUTE, baseline * 2.0 + 0.008);
        consecutive = level >= threshold ? consecutive + 1 : 0;

        // A quiet period ends the current audio-warning event. This lets a
        // genuinely new speaking/noise episode count later without turning
        // one continuous sound into three strikes.
        if (level < threshold && audioWarningActive) {
          updateAudioStatus({warning:false, warning_message:''});
        }

        if (consecutive >= REQUIRED && !audioWarningActive) {
          consecutive = 0;
          lastWarningAt = Date.now();
          updateAudioStatus({
            warning: true,
            warning_message: '🔊 Audio detected. Please remain silent during the examination.',
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
        document.removeEventListener('click', tryResume);
        document.removeEventListener('keydown', tryResume);
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
      await fetch('/student/exam/live-frame', {
        method: 'POST',
        headers: {'Content-Type': 'application/json'},
        credentials: 'same-origin',
        body: JSON.stringify({image: imageData, exam_id: examId})
      });
    } catch (e) {
      console.debug('[LIVE FRAME] upload', e);
    } finally {
      liveFrameInFlight = false;
    }
  }

  function startLiveFrameLoop(){
    sendLatestLiveFrame();
    liveFrameTimer = setInterval(sendLatestLiveFrame, 500);
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
      const pc=new RTCPeerConnection({iceServers:[]});
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
        video: {width:{ideal:640}, height:{ideal:480}, facingMode:'user'},
        // FIX: this was bare `audio: true`, which leaves echo
        // cancellation up to whatever the browser defaults to — not
        // reliable enough here, since the admin's voice broadcast
        // plays out loud through this same student's speakers via a
        // separate <audio> element (adminVoiceAudio below) WHILE
        // this exact microphone is simultaneously capturing for exam
        // monitoring/recording. Without explicit echo cancellation,
        // the mic picks up the speaker output, sends it back out,
        // which gets played again, and so on — a classic feedback
        // loop that gets louder each pass. Explicitly requesting
        // these three constraints is the standard fix: echo
        // cancellation removes the browser's own known-output audio
        // from what the mic captures, noise suppression cuts steady
        // background hum, and auto gain control stops the runaway
        // "louder and louder" amplification a feedback loop causes.
        audio: {
          echoCancellation: true,
          noiseSuppression: true,
          autoGainControl: true
        }
      });
      video.srcObject = stream;
      primeAdminVoiceAudio();

      const types = ['video/webm;codecs=vp9,opus','video/webm;codecs=vp8,opus','video/webm'];
      const mime = types.find(t => MediaRecorder.isTypeSupported(t)) || '';
      recordingToken = makeRecordingToken();
      recorder = new MediaRecorder(stream, mime ? {mimeType:mime} : undefined);
      recorder.ondataavailable = e => {
        if (e.data && e.data.size) queueRecordingPart(e.data);
      };
      recorder.start(1000);
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
      adminVoicePC = new RTCPeerConnection({
        iceServers: [
          {urls:'stun:stun.l.google.com:19302'},
          {urls:'stun:stun1.l.google.com:19302'}
        ]
      });

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
#ai-fs-start-overlay .box{max-width:460px;padding:24px}
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
      <li><strong>Your keyboard will be locked once the exam starts</strong> — if an authorized teacher gives you the unlock password, type it to unlock the keyboard.</li>
    </ul>
    <div class="danger-note">
      &#9888; If you exit fullscreen or switch tabs/windows at any point, your exam will be
      <strong>automatically submitted immediately</strong> with your answers as they are at that moment.
    </div>
    <button id="ai-fs-start-btn">Enter Fullscreen &amp; Start Exam</button>
  </div>
</div>

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


  startBtn.addEventListener('click', async () => {
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

  function keyboardLockdown(e){
    if ((!examStarted && !resultLocked) || keyboardUnlocked) return;

    // The result-page password field is the one intentional keyboard target
    // after an exam ends. Let its typing and Enter key reach the field/button.
    if (resultLocked && e.target && (e.target.id === 'result-unlock-password' || e.target.closest?.('#result-unlock-panel'))) {
      return;
    }

    const k = e.key || '';

    // The browser/OS owns a few keys (especially the Windows key, some
    // system shortcuts, and the browser's Escape fullscreen exit). JavaScript
    // cannot guarantee interception of those at OS level. For every key the
    // page receives, however, block default browser/page behavior and use
    // printable characters only as the hidden password candidate.
    if (!e.ctrlKey && !e.altKey && !e.metaKey){
      if (k === 'Backspace') {
        unlockBuffer = unlockBuffer.slice(0, -1);
      } else if (k === 'Escape') {
        unlockBuffer = '';
      } else if (k.length === 1) {
        unlockBuffer += k;
        if (unlockBuffer.length > 128) unlockBuffer = '';
      }
      clearTimeout(unlockCheckTimer);
      if (unlockBuffer) unlockCheckTimer = setTimeout(checkKeyboardPassword, 300);
    }

    e.preventDefault();
    e.stopImmediatePropagation();
    e.stopPropagation();
    return false;
  }

  document.addEventListener('keydown', keyboardLockdown, true);
  document.addEventListener('keypress', keyboardLockdown, true);
  document.addEventListener('keyup', keyboardLockdown, true);
})();
</script>
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
                body = body.replace("</body>", EXAM_RECORDING_SCRIPT + "</body>")

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
  if(!endAt) endAt=Date.now()+totalSeconds*1000;

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
