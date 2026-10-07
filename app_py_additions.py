# =====================================================================
# ADD THIS NEAR THE TOP OF app.py, next to DATABASE = "database.xlsx"
# =====================================================================

RECORDINGS_FOLDER = "recordings"


# =====================================================================
# ADD THIS ROUTE — receives and saves the student's exam video
# (put it anywhere among your other @app.route blocks, e.g. right
# after monitor_exam())
#
# NOTE ON "STORING VIDEO IN THE DATABASE":
# Video files are saved to disk (recordings/ folder), not inside
# database.xlsx. Excel/most databases are not built to hold large
# binary video data efficiently — the correct pattern (used by real
# systems too) is: file lives on disk, database stores a reference
# to it. Here, the filename itself IS that reference:
#     <student_id>_<exam_id>.webm
# so any recording can always be traced back to exactly which student
# took which exam, without needing a separate database column.
# =====================================================================

@app.route("/student/exam/<exam_id>/upload_recording", methods=["POST"])
@student_login_required
def upload_recording(exam_id):

    try:

        video_file = request.files.get("video")

        if not video_file:
            return jsonify({
                "success": False,
                "error": "No video received"
            })

        os.makedirs(RECORDINGS_FOLDER, exist_ok=True)

        student_id = session["student_id"]

        filename = f"{student_id}_{exam_id}.webm"

        filepath = os.path.join(RECORDINGS_FOLDER, filename)

        video_file.save(filepath)

        return jsonify({
            "success": True,
            "filename": filename
        })

    except Exception as e:

        print("Recording Upload Error:", str(e))

        return jsonify({
            "success": False,
            "error": str(e)
        })


# =====================================================================
# ADD THIS ROUTE — lets admin see all recordings for a given exam
# =====================================================================

@app.route("/admin/exam/<exam_id>/recordings")
# @admin_login_required   (uncomment once you enforce admin login here)
def admin_exam_recordings(exam_id):

    files = []

    if os.path.exists(RECORDINGS_FOLDER):

        for f in os.listdir(RECORDINGS_FOLDER):

            if exam_id in f:

                files.append(f)

    return render_template(
        "admin_recordings.html",
        exam_id=exam_id,
        files=files
    )


# =====================================================================
# ADD THIS ROUTE — streams the video INLINE so it plays in the browser
# (used by the <video> tag on admin_recordings.html)
# =====================================================================

@app.route("/admin/recordings/<filename>/stream")
# @admin_login_required   (uncomment once you enforce admin login here)
def admin_stream_recording(filename):

    filepath = os.path.join(RECORDINGS_FOLDER, filename)

    if not os.path.exists(filepath):

        flash("Recording not found.", "error")

        return redirect(url_for("admin_dashboard"))

    return send_file(
        filepath,
        as_attachment=False,
        mimetype="video/webm",
        conditional=True   # enables seeking/scrubbing in the video player
    )


# =====================================================================
# ADD THIS ROUTE — lets admin download one specific recording
# =====================================================================

@app.route("/admin/recordings/<filename>/download")
# @admin_login_required   (uncomment once you enforce admin login here)
def admin_download_recording(filename):

    filepath = os.path.join(RECORDINGS_FOLDER, filename)

    if not os.path.exists(filepath):

        flash("Recording not found.", "error")

        return redirect(url_for("admin_dashboard"))

    return send_file(
        filepath,
        as_attachment=True,
        download_name=filename
    )


# =====================================================================
# NOTE ON FULLSCREEN VIOLATIONS:
# No new backend route needed. student_exam.html now detects when the
# student exits fullscreen and logs it through your EXISTING
# exam_violation() route (the same one used for other violations),
# just with type: "fullscreen_exit". Check your Spyder console output
# during testing — you'll see it printed there like your other
# violation types.
# =====================================================================
