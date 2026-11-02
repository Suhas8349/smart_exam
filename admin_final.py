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


# Shared Neon PostgreSQL exam store. Excel remains the local/reporting copy for now.
# Both Render services use the same DATABASE_URL.
def _shared_db_connection():
    database_url = os.environ.get("DATABASE_URL", "").strip()
    if not database_url:
        return None
    import psycopg
    return psycopg.connect(database_url, connect_timeout=10)


def _shared_exam_rows_from_excel(rows):
    """Mirror this exam's question rows into Neon using the table's real column order."""
    conn = _shared_db_connection()
    if conn is None:
        return False
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute("""
                    SELECT column_name FROM information_schema.columns
                    WHERE table_schema = 'public' AND table_name = 'exams'
                    ORDER BY ordinal_position
                """)
                columns = [r[0] for r in cur.fetchall()]
                if len(columns) != 15:
                    raise RuntimeError(
                        f"Expected 15 columns in public.exams, found {len(columns)}"
                    )
                cur.execute("DELETE FROM public.exams WHERE exam_id = %s", (str(rows[0][0]) if rows else "",))
                if rows:
                    placeholders = ", ".join(["%s"] * len(columns))
                    column_sql = ", ".join('"' + c.replace('"', '""') + '"' for c in columns)
                    cur.executemany(
                        f"INSERT INTO public.exams ({column_sql}) VALUES ({placeholders})",
                        [tuple("" if value is None else str(value) for value in row[:15]) for row in rows]
                    )
        return True
    finally:
        conn.close()


def _shared_delete_exam(exam_id):
    conn = _shared_db_connection()
    if conn is None:
        return False
    try:
        with conn:
            with conn.cursor() as cur:
                cur.execute("DELETE FROM public.exams WHERE exam_id = %s", (str(exam_id),))
        return True
    finally:
        conn.close()


# ============================================================
# REMOTE ADMIN -> STUDENT LIVE VOICE BROADCAST
# ============================================================
# admin_app.py proxies WebRTC signaling to student_app.py.  The
# browser-to-browser audio itself uses WebRTC; the Flask endpoints
# only exchange offer/answer messages.
import threading
from pathlib import Path
from flask import render_template_string

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
    """ICE servers for WebRTC (add a TURN server through ICE_SERVERS_JSON for
    strict college firewalls)."""
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


def _live_form_extras():
    """Violation counters sent by the student server with every heartbeat/frame."""
    try: count = int(str(request.form.get("violation_count", "0") or "0"))
    except ValueError: count = 0
    return {
        "violation_count": count,
        "last_violation": str(request.form.get("last_violation", ""))[:240],
        "terminated": str(request.form.get("terminated", "false")).lower() in ("1", "true", "yes", "on"),
    }


STUDENT_SIGNAL_BASE_URL = (
    os.environ.get("STUDENT_SIGNAL_BASE_URL", "").strip().rstrip("/")
    or ("https://smart-exam-student.onrender.com" if ON_RENDER else "https://127.0.0.1:5000")
)
VOICE_SIGNAL_TOKEN = os.environ.get(
    "VOICE_SIGNAL_TOKEN", "CHANGE_THIS_SHARED_VOICE_TOKEN"
)
STUDENT_SIGNAL_VERIFY_SSL = os.environ.get(
    "STUDENT_SIGNAL_VERIFY_SSL", "true" if ON_RENDER else "false"
).strip().lower() in ("1", "true", "yes", "on")


app = Flask(__name__)

app.secret_key = "admin_teacher_management_system_secret_key"


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
def examguard_admin_ui_cleanup(response):
    try:
        if (request.method == "GET" and response.status_code == 200
                and "text/html" in response.content_type and not response.is_streamed):
            path = (request.path or "").rstrip("/")
            body = response.get_data(as_text=True)
            if path in ("/admin/login", "/login", "/admin/register", "/register"):
                script = r"""<script>
(function(){function clean(){const w=document.createTreeWalker(document.body,NodeFilter.SHOW_TEXT);let n;while(n=w.nextNode()){if((n.nodeValue||'').trim().toLowerCase()==='html')n.nodeValue='';}}if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',clean);else clean();})();
</script>"""
                if "</body>" in body and "examguard-admin-clean-html" not in body:
                    body = body.replace("</body>", "<!--examguard-admin-clean-html-->" + script + "</body>")
            if path in ("/admin/dashboard", "/dashboard"):
                script = r"""<script>
(function(){document.querySelectorAll('a,button').forEach(el=>{if((el.textContent||'').trim().toLowerCase()==='home')el.remove();});})();
</script>"""
                if "</body>" in body and "examguard-admin-dashboard-home-cleanup" not in body:
                    body = body.replace("</body>", "<!--examguard-admin-dashboard-home-cleanup-->" + script + "</body>")
            if body != response.get_data(as_text=True):
                response.set_data(body)
                response.headers["Content-Length"] = str(len(response.get_data()))
    except Exception as exc:
        print("[UI] Admin cleanup skipped:", exc)
    return response


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

# Cloudinary storage for durable recordings on Render's ephemeral filesystem.
def _cloudinary_configured():
    return all(os.environ.get(k, '').strip() for k in ('CLOUDINARY_CLOUD_NAME','CLOUDINARY_API_KEY','CLOUDINARY_API_SECRET'))

def _cloudinary_public_id(filename):
    safe = os.path.basename(str(filename or 'recording.webm'))
    stem = os.path.splitext(safe)[0]
    stem = re.sub(r'[^A-Za-z0-9_-]+', '_', stem)[:180] or 'recording'
    return 'examguard/recordings/' + stem

_CLOUD_URL_CACHE = {}
_CLOUD_URL_LOCK = threading.Lock()


def _cloudinary_delivery_url(filename, download=False):
    cloud = os.environ.get('CLOUDINARY_CLOUD_NAME', '').strip()
    flags = 'fl_attachment/' if download else ''
    return f"https://res.cloudinary.com/{cloud}/video/upload/{flags}{_cloudinary_public_id(filename)}.webm"


def _cloud_mark_present(filename):
    with _CLOUD_URL_LOCK:
        _CLOUD_URL_CACHE[os.path.basename(str(filename))] = (time.time() + 3600, True)


def _cloudinary_recording_url(filename, download=False):
    """Playable/downloadable Cloudinary URL, or '' if the video is not there.

    The old version called Cloudinary's Admin API several times per table row,
    which is slow and quickly hits the API rate limit (so recordings looked
    "missing" or the page hung). The delivery URL is deterministic from the
    file name, so a cheap CDN HEAD request (cached) is enough to confirm it.
    """
    if not filename or not _cloudinary_configured():
        return ''
    key = os.path.basename(str(filename))
    now = time.time()
    with _CLOUD_URL_LOCK:
        hit = _CLOUD_URL_CACHE.get(key)
    if hit and now < hit[0]:
        exists = hit[1]
    else:
        exists = False
        try:
            r = requests.head(_cloudinary_delivery_url(key), timeout=(3, 6), allow_redirects=True)
            exists = (r.status_code == 200)
        except Exception as exc:
            print('[CLOUDINARY] existence check failed:', key, exc)
        with _CLOUD_URL_LOCK:
            _CLOUD_URL_CACHE[key] = (now + (3600 if exists else 15), exists)
    return _cloudinary_delivery_url(key, download) if exists else ''

def _upload_recording_to_cloudinary(filepath, filename):
    if not _cloudinary_configured():
        print('[CLOUDINARY] Credentials missing; durable upload skipped')
        return False, ''
    try:
        import cloudinary
        import cloudinary.uploader
        cloudinary.config(
            cloud_name=os.environ['CLOUDINARY_CLOUD_NAME'].strip(),
            api_key=os.environ['CLOUDINARY_API_KEY'].strip(),
            api_secret=os.environ['CLOUDINARY_API_SECRET'].strip(),
            secure=True,
        )
        result = cloudinary.uploader.upload_large(
            filepath, resource_type='video', public_id=_cloudinary_public_id(filename),
            overwrite=True, chunk_size=6 * 1024 * 1024,
        )
        url = str(result.get('secure_url') or '')
        if not url:
            return False, ''
        print('[CLOUDINARY] Recording stored:', os.path.basename(filename))
        return True, url
    except Exception as exc:
        print('[CLOUDINARY] Recording upload failed:', exc)
        return False, ''


_CLOUD_UPLOADING = set()
_CLOUD_UPLOADING_LOCK = threading.Lock()


def _cloud_upload_async(path, filename):
    """Upload to Cloudinary in the background so the student's upload request
    returns immediately. Retries with back-off; a '.cloud' marker records success."""
    if not _cloudinary_configured() or not os.path.isfile(path):
        return
    with _CLOUD_UPLOADING_LOCK:
        if filename in _CLOUD_UPLOADING:
            return
        _CLOUD_UPLOADING.add(filename)

    def worker():
        try:
            for attempt in range(1, 8):
                ok, _url = _upload_recording_to_cloudinary(path, filename)
                if ok:
                    _cloud_mark_present(filename)
                    try:
                        with open(path + '.cloud', 'w') as fh: fh.write(str(time.time()))
                    except OSError:
                        pass
                    return
                time.sleep(min(90, 6 * attempt))
            print('[CLOUDINARY] giving up for now (will retry on next sweep):', filename)
        finally:
            with _CLOUD_UPLOADING_LOCK:
                _CLOUD_UPLOADING.discard(filename)
    threading.Thread(target=worker, daemon=True, name='cloud-upload').start()


def _cloud_sweep_once():
    try:
        for name in os.listdir(RECORDINGS_FOLDER):
            if not name.lower().endswith('.webm') or name.endswith('.partial.webm'):
                continue
            p = os.path.join(RECORDINGS_FOLDER, name)
            if os.path.isfile(p) and not os.path.isfile(p + '.cloud') and os.path.getsize(p) > 1024:
                _cloud_upload_async(p, name)
    except Exception as exc:
        print('[CLOUDINARY] sweep error:', exc)


def _start_cloud_sweeper():
    if not _cloudinary_configured():
        return
    def loop():
        while True:
            _cloud_sweep_once()
            time.sleep(300)
    threading.Thread(target=loop, daemon=True, name='cloud-sweeper').start()


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



# ============================================================
# EXAM CHANGE NOTIFICATION + SOFT DELETE
# ============================================================
# Shared Neon mode: both services already see the same workbook and the
# student dashboard notices the new `exams_version` within a second.
# Local mode (no DATABASE_URL, e.g. two PCs on one Wi-Fi): this admin pushes
# the Exams sheet straight to the student service every time it changes.
USE_PUBLIC_EXAMS_TABLE = False   # the old public.exams mirror is superseded

import hashlib as _eg_hashlib
_EXAM_PUSH_EVENT = threading.Event()
_EXAM_PUSH_STATE = {"hash": "", "started": False}
_EXAM_PUSH_LOCK = threading.Lock()


def _exam_rows_for_push():
    wb = load_database(read_only=True, data_only=True)
    try:
        if "Exams" not in wb.sheetnames:
            return []
        rows = []
        for row in wb["Exams"].iter_rows(min_row=2, values_only=True):
            if not row or row[0] in (None, ""):
                continue
            rows.append([
                (v.strftime("%Y-%m-%dT%H:%M") if hasattr(v, "strftime") else v)
                for v in row[:15]
            ])
        return rows
    finally:
        wb.close()


def _push_exams_to_student_once(force=False):
    """Local mode only. Returns True when the student service is up to date."""
    if _eg_use_neon():
        return True
    rows = _exam_rows_for_push()
    digest = _eg_hashlib.sha1(json.dumps(rows, sort_keys=True, default=str).encode("utf-8")).hexdigest()
    if not force and digest == _EXAM_PUSH_STATE["hash"]:
        return True
    r = requests.post(
        f"{STUDENT_SIGNAL_BASE_URL}/internal/sync/exams",
        json={"rows": rows},
        headers={"X-ExamGuard-Sync-Token": RECORDING_SYNC_TOKEN},
        timeout=(4, 20),
        verify=STUDENT_SIGNAL_VERIFY_SSL,
    )
    ok = bool(r.ok and (r.json() if r.content else {}).get("success"))
    if ok:
        _EXAM_PUSH_STATE["hash"] = digest
        print(f"[EXAM-SYNC] Student service updated ({len(rows)} exam rows)")
    else:
        print("[EXAM-SYNC] Student service rejected the exam list:", r.status_code)
    return ok


def _exam_push_loop():
    failed = True
    while True:
        triggered = _EXAM_PUSH_EVENT.wait(timeout=3 if failed else 20)
        _EXAM_PUSH_EVENT.clear()
        try:
            failed = not _push_exams_to_student_once(force=bool(triggered) or failed)
        except Exception as exc:
            failed = True
            print("[EXAM-SYNC] Student not reachable yet:", exc)
            time.sleep(2)


def _start_exam_push_thread():
    if _eg_use_neon():
        return
    with _EXAM_PUSH_LOCK:
        if _EXAM_PUSH_STATE["started"]:
            return
        _EXAM_PUSH_STATE["started"] = True
    threading.Thread(target=_exam_push_loop, daemon=True, name="exam-push").start()



def _migrate_public_exams_once():
    """One time: bring exams that only exist in the old public.exams mirror
    (created from the admin site before the databases were unified) into the
    shared workbook, so students can finally see them."""
    if not _eg_use_neon():
        return
    wb = load_database()
    try:
        if "Meta" in wb.sheetnames and any(
                r and r[0] == "public_exams_migrated" for r in wb["Meta"].iter_rows(values_only=True)):
            return
        rows = []
        conn = None
        try:
            conn = _eg_conn()
            with conn.cursor() as cur:
                cur.execute("SELECT * FROM public.exams")
                rows = cur.fetchall()
        except Exception:
            rows = []
        finally:
            if conn is not None:
                try:
                    conn.close()
                except Exception:
                    pass
        have = {str(r[0]).strip() for r in wb["Exams"].iter_rows(min_row=2, values_only=True) if r and r[0]}
        archived = set()
        if "ArchivedExams" in wb.sheetnames:
            archived = {str(r[0]).strip() for r in wb["ArchivedExams"].iter_rows(min_row=2, values_only=True) if r and r[0]}
        added = 0
        for row in rows:
            if len(row) < 15:
                continue
            exam_id = str(row[0]).strip()
            if not exam_id or exam_id in have or exam_id in archived:
                continue
            vals = list(row[:15])
            for idx in (5, 14):
                try:
                    vals[idx] = int(str(vals[idx]).strip())
                except (TypeError, ValueError):
                    pass
            wb["Exams"].append(vals)
            added += 1
        meta = wb["Meta"] if "Meta" in wb.sheetnames else wb.create_sheet("Meta")
        meta.append(["public_exams_migrated", datetime.now().isoformat(), added])
        save_database(wb)
        print(f"[MIGRATE] Imported {added} exam row(s) from the old public.exams mirror")
    finally:
        wb.close()


def notify_exams_changed():
    """Call after any exam was created, edited or removed."""
    _EG_VERSION_CACHE["t"] = 0.0
    if not _eg_use_neon():
        _start_exam_push_thread()
        _EXAM_PUSH_EVENT.set()


def _archive_exam_rows(workbook, rows, who):
    """Keep a permanent copy of removed exam rows in the ArchivedExams sheet."""
    if "ArchivedExams" not in workbook.sheetnames:
        ws = workbook.create_sheet("ArchivedExams")
        header = [c.value for c in workbook["Exams"][1]]
        ws.append(header + ["Archived At", "Archived By"])
    else:
        ws = workbook["ArchivedExams"]
    stamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    for row in rows:
        ws.append(list(row) + [stamp, who])


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
        <h1 style="font-size:32px;margin:0 0 36px;color:#f1f0f7;background:linear-gradient(120deg,#f1f0f7 40%,#9d85ff);-webkit-background-clip:text;background-clip:text;-webkit-text-fill-color:transparent;">Exam Management System</h1>

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
    exams = {}

    # Single source of truth: the shared workbook (Neon on Render).
    if USE_PUBLIC_EXAMS_TABLE and os.environ.get("DATABASE_URL", "").strip():
        conn = None
        try:
            conn = _shared_db_connection()
            if conn is None:
                raise RuntimeError("DATABASE_URL is not configured")
            with conn.cursor() as cur:
                cur.execute("SELECT * FROM public.exams")
                rows = cur.fetchall()

            for row in rows:
                if len(row) < 15:
                    continue
                if str(row[1]).strip() != str(teacher_id).strip():
                    continue
                exam_id = row[0]
                if exam_id not in exams:
                    exams[exam_id] = {
                        "exam_id": exam_id,
                        "subject_name": row[3],
                        "subject_code": row[4],
                        "teacher_name": row[2],
                        "question_count": 0,
                    }
                exams[exam_id]["question_count"] += 1
        except Exception:
            app.logger.exception("Failed to load teacher dashboard exams from Neon")
            flash("Could not load exams from the shared database. Please try again.", "error")
        finally:
            if conn is not None:
                conn.close()
    else:
        # Keep Excel behavior for local development without DATABASE_URL.
        workbook = load_database()
        try:
            sheet = workbook["Exams"]
            for row in sheet.iter_rows(min_row=2, values_only=True):
                exam_id = row[0]
                if str(row[1]).strip() != str(teacher_id).strip():
                    continue
                if exam_id not in exams:
                    exams[exam_id] = {
                        "exam_id": exam_id,
                        "subject_name": row[3],
                        "subject_code": row[4],
                        "teacher_name": row[2],
                        "question_count": 0,
                    }
                exams[exam_id]["question_count"] += 1
        finally:
            workbook.close()

    exam_list = list(exams.values())
    exam_list.reverse()
    return render_template("dashboard.html", exams=exam_list)


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

        notify_exams_changed()   # students see the new exam within a second

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
    exams = {}

    # Single source of truth: the shared workbook (Neon on Render).
    if USE_PUBLIC_EXAMS_TABLE and os.environ.get("DATABASE_URL", "").strip():
        conn = None
        try:
            conn = _shared_db_connection()
            if conn is None:
                raise RuntimeError("DATABASE_URL is not configured")
            with conn.cursor() as cur:
                cur.execute("SELECT * FROM public.exams")
                rows = cur.fetchall()

            for row in rows:
                if len(row) < 15 or str(row[1]).strip() != str(teacher_id).strip():
                    continue
                exam_id = row[0]
                exams.setdefault(exam_id, {
                    "exam_id": exam_id,
                    "subject_name": row[3],
                    "subject_code": row[4],
                    "question_count": 0,
                    "duration_minutes": row[14] if row[14] else 30,
                })
                exams[exam_id]["question_count"] += 1
        except Exception:
            app.logger.exception("Failed to load managed exams from Neon")
            flash("Could not load exams from the shared database. Please try again.", "error")
        finally:
            if conn is not None:
                conn.close()
    else:
        # Keep Excel behavior for local development without DATABASE_URL.
        workbook = load_database()
        try:
            sheet = workbook["Exams"]
            for row in sheet.iter_rows(min_row=2, values_only=True):
                if str(row[1]).strip() != str(teacher_id).strip():
                    continue
                exams.setdefault(row[0], {
                    "exam_id": row[0], "subject_name": row[3],
                    "subject_code": row[4], "question_count": 0,
                    "duration_minutes": row[14] if len(row) > 14 and row[14] else 30,
                })
                exams[row[0]]["question_count"] += 1
        finally:
            workbook.close()

    return render_template("manage_exams.html", exams=list(exams.values()))


# ============================================================
# EDIT / MANAGE AN ALREADY-CREATED EXAM
# ============================================================

@app.route("/teacher/exam/<exam_id>/delete", methods=["POST"])
@teacher_login_required
def delete_exam(exam_id):
    """Remove an exam from the dashboards.

    The exam is never destroyed: its question rows move to the ArchivedExams
    sheet, and every result / recording that exists stays exactly where it is.
    Having results or recordings does NOT block removal.
    """
    teacher_id = str(session.get("teacher_id", "")).strip()
    wanted = str(exam_id).strip()
    workbook = load_database()
    try:
        exam_sheet = workbook["Exams"]
        row_numbers, removed_rows, other_owner = [], [], False
        for excel_row, row in enumerate(exam_sheet.iter_rows(min_row=2, values_only=True), start=2):
            if str(row[0] if row else "").strip() != wanted:
                continue
            if str(row[1] or "").strip() == teacher_id:
                row_numbers.append(excel_row)
                removed_rows.append(row)
            else:
                other_owner = True

        if not row_numbers:
            workbook.close()
            if other_owner:
                flash("You can only remove exams that you created.", "error")
            else:
                flash("This exam was already removed.", "success")
            return redirect(url_for("manage_exams"))

        _archive_exam_rows(workbook, removed_rows, teacher_id)
        for excel_row in reversed(row_numbers):
            exam_sheet.delete_rows(excel_row, 1)
        save_database(workbook)
    except Exception as exc:
        app.logger.exception("Exam removal failed")
        flash(f"Could not remove the exam: {exc}", "error")
        return redirect(url_for("manage_exams"))
    finally:
        try:
            workbook.close()
        except Exception:
            pass

    notify_exams_changed()
    flash(f"Exam {exam_id} removed. Its results and recordings are still stored safely.", "success")
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
        if str(row[0] or "").strip() == str(exam_id).strip() and str(row[1] or "").strip() == str(teacher_id).strip():
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
        notify_exams_changed()   # students see the change within a second
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
        os.makedirs(RECORDINGS_FOLDER,exist_ok=True); target=os.path.join(RECORDINGS_FOLDER,fn); temp=target+f".{uuid.uuid4().hex[:8]}.uploading"; up.save(temp)
        with open(temp,"rb") as fh: magic=fh.read(4)
        if os.path.getsize(temp)<1024 or magic!=bytes((0x1a,0x45,0xdf,0xa3)):
            os.remove(temp); temp=None; return jsonify({"success":False,"error":"Invalid WebM recording"}),400
        os.replace(temp,target); temp=None
        cloud_url = ""
        _cloud_upload_async(target, fn)   # background; the student is not kept waiting

        # If the result arrived before the recording, attach the confirmed
        # filename now so the admin recordings/results screens do not retain
        # an empty or stale Recording File value.
        wb = None
        try:
            if os.path.isfile(DATABASE) and _valid_xlsx(DATABASE):
                wb = load_database()
                if "Results" in wb.sheetnames:
                    ws = wb["Results"]
                    headers = [cell.value for cell in ws[1]]
                    if "Recording File" not in headers:
                        ws.cell(row=1, column=ws.max_column + 1, value="Recording File")
                        headers = [cell.value for cell in ws[1]]
                    if "Student ID" in headers and "Exam ID" in headers:
                        sid_col = headers.index("Student ID") + 1
                        exam_col = headers.index("Exam ID") + 1
                        file_col = headers.index("Recording File") + 1
                        matched = False
                        for row_num in range(2, ws.max_row + 1):
                            if (str(ws.cell(row_num, sid_col).value or "") == student_id
                                    and str(ws.cell(row_num, exam_col).value or "") == exam_id):
                                ws.cell(row_num, file_col, fn)
                                matched = True
                        if matched:
                            save_database(wb)
                if wb is not None:
                    wb.close()
                    wb = None
        except Exception as db_exc:
            print("[SYNC] Recording saved but result-link update failed:", db_exc)
            try:
                if wb is not None: wb.close()
            except Exception: pass

        print(f"[SYNC] Recording received and linked: {fn} ({student_id}/{exam_id})")
        return jsonify({"success":True,"filename":fn,"size":os.path.getsize(target),"durable":False,"cloud_pending":_cloudinary_configured(),"recording_url":""})
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
        payload=request.get_json(silent=True) or {}
        wb=load_database()
        if _eg_use_neon():
            # Student and admin share one database: the result is already
            # there. Only the recording file name may still need attaching.
            _rid = str(payload.get("result_id", "")).strip()
            _ws = wb["Results"] if "Results" in wb.sheetnames else None
            if _ws is not None and _rid:
                _hdr = [c.value for c in _ws[1]]
                if "Result ID" in _hdr:
                    _rc = _hdr.index("Result ID")
                    _fc = _hdr.index("Recording File") if "Recording File" in _hdr else None
                    _want = _safe_sync_filename(payload.get("recording_file")) if payload.get("recording_file") else ""
                    for _r in _ws.iter_rows(min_row=2, values_only=True):
                        if len(_r) > _rc and str(_r[_rc] or "") == _rid:
                            _have = str(_r[_fc] or "") if (_fc is not None and len(_r) > _fc) else ""
                            if not _want or _have == _want:
                                wb.close()
                                return jsonify({"success": True, "result_id": _rid, "shared": True})
                            break
        _upsert_admin_sync_result(wb,payload)
        # If the video arrived first, attach it while inserting/upserting the result.
        recording_name = str(payload.get("recording_file", "") or "").strip()
        if not recording_name:
            sid_safe = re.sub(r"[^A-Za-z0-9._-]+", "_", str(payload.get("student_id", "")))[:100] or "student"
            exam_safe = re.sub(r"[^A-Za-z0-9._-]+", "_", str(payload.get("exam_id", "")))[:100] or "exam"
            candidate = _safe_sync_filename(f"{sid_safe}_{exam_safe}.webm")
            if os.path.isfile(os.path.join(RECORDINGS_FOLDER, candidate)):
                recording_name = candidate
        if recording_name and "Results" in wb.sheetnames:
            ws = wb["Results"]
            headers = [cell.value for cell in ws[1]]
            if "Recording File" not in headers:
                ws.cell(row=1, column=ws.max_column + 1, value="Recording File")
                headers = [cell.value for cell in ws[1]]
            rid_col = headers.index("Result ID") + 1
            file_col = headers.index("Recording File") + 1
            for row_num in range(2, ws.max_row + 1):
                if str(ws.cell(row_num, rid_col).value or "") == str(payload.get("result_id", "")):
                    ws.cell(row_num, file_col, recording_name)
                    break
        save_database(wb)
        wb.close()
        return jsonify({"success":True,"result_id":payload.get("result_id","")})
    except Exception as e:
        try: wb.close()
        except Exception: pass
        return jsonify({"success":False,"error":str(e)}),500

_REC_TOKEN_LOCKS = {}
_REC_TOKEN_LOCKS_GUARD = threading.Lock()


class _RecTokenLock:
    """Serialise chunk assembly for one recording (threads and, on Linux, processes)."""
    def __init__(self, token):
        with _REC_TOKEN_LOCKS_GUARD:
            self.tl = _REC_TOKEN_LOCKS.setdefault(token, threading.Lock())
        self.token = token
        self.fh = None

    def __enter__(self):
        self.tl.acquire()
        try:
            import fcntl
            os.makedirs(RECORDING_PARTS_FOLDER, exist_ok=True)
            self.fh = open(os.path.join(RECORDING_PARTS_FOLDER, f".{self.token}.lock"), "a+")
            fcntl.flock(self.fh, fcntl.LOCK_EX)
        except Exception:
            self.fh = None
        return self

    def __exit__(self, *exc):
        try:
            if self.fh is not None:
                import fcntl
                fcntl.flock(self.fh, fcntl.LOCK_UN)
                self.fh.close()
        except Exception:
            pass
        self.tl.release()
        return False


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
        with _RecTokenLock(token):
            return _store_recording_chunk(exam_id, student_id, filename, token, seq, chunk)
    except Exception as e:
        print("[SYNC] recording chunk error:", e)
        return jsonify({"success": False, "error": str(e)}), 500


def _store_recording_chunk(exam_id, student_id, filename, token, seq, chunk):
    try:
        token_dir = os.path.join(RECORDING_PARTS_FOLDER, token)
        os.makedirs(token_dir, exist_ok=True)
        meta_path = os.path.join(token_dir, "meta.json")
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
    """Assemble chunk-synced recordings (the student normally sends one complete
    file via /internal/sync/recording; this path is the chunked alternative)."""
    if not _sync_token_valid(request.headers.get("X-ExamGuard-Sync-Token", "")):
        return jsonify({"success": False, "error": "Unauthorized recording sync"}), 401
    partial = None
    _lk = None
    try:
        exam_id = str(request.form.get("exam_id", "")).strip()
        student_id = str(request.form.get("student_id", "")).strip()
        filename = _safe_sync_filename(request.form.get("filename", ""))
        token = str(request.form.get("recording_token", "")).strip()
        expected_raw = str(request.form.get("expected_last_seq", "")).strip()
        expected = int(expected_raw) if expected_raw.isdigit() else None
        if not exam_id or not student_id or not token:
            return jsonify({"success": False, "error": "Missing recording finalize data"}), 400
        if not re.fullmatch(r"[A-Za-z0-9_-]{16,80}", token):
            return jsonify({"success": False, "error": "Invalid token"}), 400
        _lk = _RecTokenLock(token)
        _lk.__enter__()
        token_dir = os.path.join(RECORDING_PARTS_FOLDER, token)
        meta_path = os.path.join(token_dir, "meta.json")
        done_target = os.path.join(RECORDINGS_FOLDER, filename)
        if (not os.path.isdir(token_dir)) and os.path.isfile(done_target) and os.path.getsize(done_target) > 1024:
            return jsonify({"success": True, "filename": filename, "already": True})
        if not os.path.isdir(token_dir) or not os.path.isfile(meta_path):
            return jsonify({"success": False, "error": "Recording chunks not found", "retry": True}), 409
        with open(meta_path, "r", encoding="utf-8") as fh:
            meta = json.load(fh)
        if str(meta.get("student_id", "")) != student_id or str(meta.get("exam_id", "")) != exam_id:
            return jsonify({"success": False, "error": "Recording metadata mismatch"}), 403

        target = os.path.join(RECORDINGS_FOLDER, filename)
        partial = target + ".uploading"
        progressive = target + ".partial.webm"

        # The chunk endpoint appends contiguous parts to the progressive file
        # and deletes them, remembering how far it got in assembled_seq.txt.
        seq_marker = os.path.join(token_dir, "assembled_seq.txt")
        next_seq = 0
        if os.path.isfile(seq_marker):
            try: next_seq = int(Path(seq_marker).read_text(encoding="utf-8").strip() or "0")
            except Exception: next_seq = 0
        while os.path.isfile(os.path.join(token_dir, f"{next_seq:08d}.part")):
            with open(progressive, "ab") as out_file, open(os.path.join(token_dir, f"{next_seq:08d}.part"), "rb") as src:
                shutil.copyfileobj(src, out_file, length=1024 * 1024)
            try: os.remove(os.path.join(token_dir, f"{next_seq:08d}.part"))
            except OSError: pass
            next_seq += 1
        try: Path(seq_marker).write_text(str(next_seq), encoding="utf-8")
        except Exception: pass

        if expected is not None and next_seq <= expected:
            return jsonify({"success": False, "retry": True, "next_seq": next_seq,
                            "missing_sequences": list(range(next_seq, min(expected + 1, next_seq + 80)))}), 409
        if not os.path.isfile(progressive) or os.path.getsize(progressive) < 1024:
            return jsonify({"success": False, "error": "Recording is empty", "retry": True}), 409
        with open(progressive, "rb") as fh:
            magic = fh.read(4)
        if magic != bytes((0x1a, 0x45, 0xdf, 0xa3)):
            return jsonify({"success": False, "error": "Recording is not a valid WebM"}), 400

        os.replace(progressive, target)
        partial = None
        shutil.rmtree(token_dir, ignore_errors=True)
        _cloud_upload_async(target, filename)
        print(f"[SYNC] Recording finalized on admin: {filename} ({student_id}/{exam_id})")
        return jsonify({"success": True, "filename": filename, "size": os.path.getsize(target), "durable": False})
    except Exception as e:
        print("[SYNC] recording finalize error:", e)
        try:
            if partial and os.path.isfile(partial): os.remove(partial)
        except Exception:
            pass
        return jsonify({"success": False, "error": str(e)}), 500
    finally:
        if _lk is not None:
            _lk.__exit__(None, None, None)


@app.route("/internal/sync/live-heartbeat", methods=["POST"])
def internal_sync_live_heartbeat():
    token = str(request.headers.get("X-ExamGuard-Live-Token", "")).strip()
    if not LIVE_SYNC_TOKEN or token != LIVE_SYNC_TOKEN:
        return jsonify({"success":False,"error":"Unauthorized live heartbeat"}),401
    tmp=None
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
            "status":str(request.form.get("status","")),
            "warning":str(request.form.get("warning","false")).lower() in ("1","true","yes","on"),
            "warning_message":str(request.form.get("warning_message","")),
            **_live_form_extras(),
        }
        tmp=os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}.json.uploading")
        with open(tmp,"w",encoding="utf-8") as fh: json.dump(status,fh)
        os.replace(tmp,os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}.json"))
        print(f"[LIVE] heartbeat received: {student_id} / {status['exam_id']}")
        return jsonify({"success":True})
    except Exception as e:
        try:
            if tmp and os.path.exists(tmp): os.remove(tmp)
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
            **_live_form_extras(),
        }
        status_tmp=os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}.json.uploading")
        with open(status_tmp,"w",encoding="utf-8") as fh: json.dump(status,fh)
        os.replace(status_tmp,os.path.join(LIVE_FRAMES_FOLDER,f"{safe_id}.json"))
        print(f"[LIVE] frame received: {student_id} / {status['exam_id']}")
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
        recording_available = bool(safe_recording and (os.path.isfile(os.path.join(RECORDINGS_FOLDER, safe_recording)) or _cloudinary_recording_url(safe_recording)))

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
            "recording_url": (url_for("admin_stream_recording", filename=safe_recording) if os.path.isfile(os.path.join(RECORDINGS_FOLDER, safe_recording)) else _cloudinary_recording_url(safe_recording)) if recording_available else "",
            "recording_download_url": (url_for("admin_download_recording", filename=safe_recording) if os.path.isfile(os.path.join(RECORDINGS_FOLDER, safe_recording)) else _cloudinary_recording_url(safe_recording)) if recording_available else "",
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
        available = bool(recording_file and (os.path.isfile(os.path.join(RECORDINGS_FOLDER, recording_file)) or _cloudinary_recording_url(recording_file)))

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
            "recording_url": (url_for("admin_stream_recording", filename=recording_file) if os.path.isfile(os.path.join(RECORDINGS_FOLDER, recording_file)) else _cloudinary_recording_url(recording_file)) if available else "",
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
    subjects = {}
    conn = None

    # Single source of truth: the shared workbook (Neon on Render).
    if USE_PUBLIC_EXAMS_TABLE and os.environ.get("DATABASE_URL", "").strip():
        try:
            conn = _shared_db_connection()
            if conn is not None:
                with conn.cursor() as cur:
                    cur.execute("""
                        SELECT DISTINCT exam_id, teacher_name, subject_name, subject_code
                        FROM public.exams
                        ORDER BY subject_code, subject_name, exam_id
                    """)
                    rows = cur.fetchall()
                for exam_id, teacher_name, subject_name, subject_code in rows:
                    key = subject_code or subject_name or "Unknown"
                    if key not in subjects:
                        subjects[key] = {
                            "subject_code": subject_code,
                            "subject_name": subject_name,
                            "teacher_names": set(),
                            "exam_ids": [],
                        }
                    if teacher_name:
                        subjects[key]["teacher_names"].add(teacher_name)
                    if exam_id and exam_id not in subjects[key]["exam_ids"]:
                        subjects[key]["exam_ids"].append(exam_id)
        except Exception:
            app.logger.exception("Could not load Admin dashboard exams from Neon")
            subjects.clear()
        finally:
            if conn is not None:
                conn.close()

    # Fallback for local development when DATABASE_URL is not configured,
    # or if the shared database query fails.
    if not subjects:
        workbook = load_database(read_only=True, data_only=True)
        try:
            exam_sheet = workbook["Exams"]
            for row in exam_sheet.iter_rows(min_row=2, values_only=True):
                exam_id = row[0]
                teacher_name = row[2]
                subject_name = row[3]
                subject_code = row[4]
                key = subject_code or subject_name or "Unknown"
                if key not in subjects:
                    subjects[key] = {
                        "subject_code": subject_code,
                        "subject_name": subject_name,
                        "teacher_names": set(),
                        "exam_ids": [],
                    }
                if teacher_name:
                    subjects[key]["teacher_names"].add(teacher_name)
                if exam_id and exam_id not in subjects[key]["exam_ids"]:
                    subjects[key]["exam_ids"].append(exam_id)
        finally:
            workbook.close()

    for subject in subjects.values():
        subject["teacher_names"] = ", ".join(sorted(subject["teacher_names"]))

    return render_template("admin_dashboard.html", subjects=list(subjects.values()))


ADMIN_LOGIN_HTML = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Admin Login</title>
<style>
  *{box-sizing:border-box}
  body{margin:0;min-height:100vh;display:flex !important;align-items:center !important;justify-content:center !important;background:radial-gradient(circle at 20% 10%,#2a2150,#0a0e1a 55%);font-family:'Segoe UI',Arial,sans-serif;color:#f1f0f7}
  .box{width:min(400px,92vw);padding:34px 30px;border-radius:18px;background:rgba(20,24,42,.82);border:1px solid rgba(157,133,255,.3);box-shadow:0 20px 60px rgba(0,0,0,.5)}
  .eyebrow{font:600 11px monospace;letter-spacing:.08em;text-transform:uppercase;color:#9d85ff;margin-bottom:8px}
  h1{margin:0 0 18px;font-size:26px}
  label{display:block;margin:14px 0 6px;font-size:13px;color:#b7b3cc}
  input{width:100%;padding:12px 14px;border-radius:10px;border:1px solid #2c3454;background:#0e1325;color:#f1f0f7;font-size:15px;outline:none}
  input:focus{border-color:#9d85ff}
  button{width:100%;margin-top:22px;padding:13px;border:0;border-radius:10px;background:linear-gradient(135deg,#7c5cff,#ff6fa4);color:#fff;font-weight:700;font-size:15px;cursor:pointer}
  .err{margin:0 0 12px;padding:10px 12px;border-radius:8px;background:#32191d;border:1px solid #5c2a2a;color:#fca5a5;font-size:13.5px}
  .ok{margin:0 0 12px;padding:10px 12px;border-radius:8px;background:#143322;border:1px solid #245c3a;color:#86efac;font-size:13.5px}
</style>
</head>
<body>
  <div class="box">
    <div class="eyebrow">Oversight Access</div>
    <h1>Admin Login</h1>
    {% with messages = get_flashed_messages(with_categories=true) %}
      {% for category, message in messages %}
        <div class="{{ 'ok' if category == 'success' else 'err' }}">{{ message }}</div>
      {% endfor %}
    {% endwith %}
    <form method="POST" autocomplete="off">
      <label for="admin_id">Admin ID</label>
      <input type="text" id="admin_id" name="admin_id" required autofocus>
      <label for="password">Password</label>
      <input type="password" id="password" name="password" required>
      <button type="submit">Login</button>
    </form>
  </div>
</body>
</html>
"""


@app.route("/admin/login", methods=["GET", "POST"])
def admin_login():
    """Single-admin login. There is intentionally no registration."""
    if request.method == "POST":
        admin_id = request.form.get("admin_id", "").strip()
        password = request.form.get("password", "")
        found = None
        workbook = load_database()
        try:
            for row in workbook["Admins"].iter_rows(min_row=2, values_only=True):
                if str(row[0]).strip() != admin_id:
                    continue
                stored = str(row[3] if len(row) > 3 and row[3] is not None else "")
                ok = False
                if stored.startswith(("scrypt:", "pbkdf2:")):
                    try: ok = check_password_hash(stored, password)
                    except Exception: ok = False
                else:
                    ok = hmac.compare_digest(stored, password)
                if ok:
                    found = row
                    break
        finally:
            workbook.close()
        if found:
            session["admin_id"] = found[0]
            session["admin_name"] = found[1]
            session["admin_email"] = found[2]
            return redirect(url_for("admin_dashboard"))
        flash("Invalid Admin ID or password.", "error")
    return render_template_string(ADMIN_LOGIN_HTML)


# ==========================================
# ADMIN LOGOUT
# ==========================================




@app.route("/admin/register", methods=["GET", "POST"])
def admin_register():
    # Admin account creation is disabled; retain only the existing admin login.
    flash("Admin registration is disabled.", "error")
    return redirect(url_for("admin_login"))

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


def _own_recording_prefixes(student_id):
    sid = str(student_id or "").strip()
    a = "".join(c for c in sid if c.isalnum() or c in "-_")
    b = re.sub(r"[^A-Za-z0-9._-]+", "_", sid)[:100]
    return tuple(x + "_" for x in {a, b} if x)


def _recording_entries_for_subject(exam_id):
    """All finished attempts of the subject that `exam_id` belongs to.

    Every entry is tied to exactly one student's Results row. A recording is
    only attached to an entry when its file name starts with THAT student's own
    id, so one student's video can never show up under another student.
    """
    entries, subject_code, subject_name = [], "", ""
    wb = load_database(read_only=True, data_only=True)
    try:
        wanted_exam = str(exam_id).strip()
        if "Exams" in wb.sheetnames:
            for row in wb["Exams"].iter_rows(min_row=2, values_only=True):
                if row and str(row[0] or "").strip() == wanted_exam:
                    subject_name = str(row[3] or "")
                    subject_code = str(row[4] or "")
                    break
        if "Results" not in wb.sheetnames:
            return entries, subject_name, subject_code
        ws = wb["Results"]
        headers = [c.value for c in ws[1]]
        hi = {name: i for i, name in enumerate(headers) if name is not None}
        rows = list(ws.iter_rows(min_row=2, values_only=True))

        def cell(row, col, default=""):
            idx = hi.get(col)
            if idx is None or idx >= len(row) or row[idx] is None:
                return default
            return row[idx]

        if not subject_code:
            for row in rows:
                if str(cell(row, "Exam ID")).strip() == wanted_exam:
                    subject_code = str(cell(row, "Subject Code"))
                    subject_name = subject_name or str(cell(row, "Subject Name"))
                    break

        for row in rows:
            same_exam = str(cell(row, "Exam ID")).strip() == wanted_exam
            same_subject = bool(subject_code) and str(cell(row, "Subject Code")).strip() == subject_code
            if not (same_exam or same_subject):
                continue
            student_id = str(cell(row, "Student ID")).strip()
            recording_name = os.path.basename(str(cell(row, "Recording File")).strip())
            if recording_name and not recording_name.startswith(_own_recording_prefixes(student_id)):
                recording_name = ""          # not this student's file: never show it
            path = os.path.join(RECORDINGS_FOLDER, recording_name) if recording_name else ""
            cloud = _cloudinary_recording_url(recording_name) if recording_name else ""
            have_file = bool(recording_name) and os.path.isfile(path)
            entries.append({
                "student_id": student_id,
                "student_name": cell(row, "Student Name", "Unknown"),
                "student_email": cell(row, "Student Email", ""),
                "subject_name": cell(row, "Subject Name", subject_name),
                "exam_id": str(cell(row, "Exam ID")),
                "submitted_at": cell(row, "Submitted At", ""),
                "percentage": cell(row, "Percentage", ""),
                "exam_status": cell(row, "Exam Status", ""),
                "filename": recording_name if (have_file or cloud) else "",
                "recording_url": cloud if (recording_name and not have_file) else "",
                "recording_missing": (not recording_name) or not (have_file or cloud),
            })
    finally:
        wb.close()
    entries.sort(key=lambda e: str(e.get("submitted_at", "")), reverse=True)
    return entries, subject_name, subject_code


ADMIN_RECORDINGS_PAGE = r"""<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Exam Recordings</title>
<style>
 body{font-family:'Segoe UI',Arial,sans-serif;background:#faf8f5;color:#201a2e;margin:0;padding:28px}
 .wrap{max-width:980px;margin:0 auto}
 h1{margin:0 0 4px;font-size:26px}
 .sub{color:#655f73;margin:0 0 22px}
 .panel{background:#fff;border:1px solid #e7e1f2;border-radius:12px;padding:18px;margin-bottom:18px}
 label{font-weight:600;font-size:14px;display:block;margin-bottom:8px}
 select{width:100%;max-width:520px;padding:11px 12px;border:1px solid #cfc7e3;border-radius:8px;font-size:15px;background:#fff}
 .btn{display:inline-block;padding:9px 16px;background:#7c5cff;color:#fff;border:0;border-radius:8px;text-decoration:none;font-weight:600;font-size:14px;cursor:pointer}
 .btn.alt{background:#e7e1f2;color:#201a2e}
 .meta{display:flex;flex-wrap:wrap;gap:8px 22px;color:#655f73;font-size:13.5px;margin:6px 0 14px}
 video{width:100%;max-height:520px;background:#000;border-radius:10px}
 .warn{background:#fff4e5;border:1px solid #f5c58a;color:#8a4b00;padding:12px 14px;border-radius:8px;font-size:14px}
 .empty{color:#8a8398}
</style></head><body><div class="wrap">
<h1>Exam Recordings</h1>
<p class="sub">{{ subject_name or 'Subject' }}{% if subject_code %} ({{ subject_code }}){% endif %}</p>

<form class="panel" method="get">
  <label for="student_id">Choose a student</label>
  <select id="student_id" name="student_id" onchange="this.form.submit()">
    <option value="">- Select a student -</option>
    {% for st in students %}
      <option value="{{ st.student_id }}" {% if st.student_id == selected %}selected{% endif %}>
        {{ st.student_name }} ({{ st.student_id }}){% if st.student_email %} - {{ st.student_email }}{% endif %}
      </option>
    {% endfor %}
  </select>
  <noscript><button class="btn" type="submit">Show recording</button></noscript>
</form>

{% if not students %}
  <div class="panel empty">No student has completed this subject yet.</div>
{% elif not selected %}
  <div class="panel empty">Select a student above to see only that student's recording for this subject.</div>
{% elif not shown %}
  <div class="panel empty">This student has no attempt for this subject.</div>
{% else %}
  {% for e in shown %}
  <div class="panel">
    <h3 style="margin:0">{{ e.student_name }} <span style="color:#8a8398;font-weight:400">({{ e.student_id }})</span></h3>
    <div class="meta">
      <span>Exam: {{ e.exam_id }}</span>
      {% if e.submitted_at %}<span>Submitted: {{ e.submitted_at }}</span>{% endif %}
      {% if e.exam_status %}<span>Status: {{ e.exam_status }}</span>{% endif %}
      {% if e.percentage != '' %}<span>Score: {{ e.percentage }}%</span>{% endif %}
    </div>
    {% if e.filename %}
      <video controls preload="metadata" src="{{ e.recording_url or url_for('admin_stream_recording', filename=e.filename) }}"></video>
      <p><a class="btn" href="{{ url_for('admin_download_recording', filename=e.filename) }}">Download</a></p>
    {% elif e.recording_missing %}
      <div class="warn">The recording for this attempt has not arrived yet. If the student only just finished, refresh in a minute. It uploads in the background.</div>
    {% endif %}
  </div>
  {% endfor %}
{% endif %}
<p><a class="btn alt" href="{{ url_for('admin_dashboard') }}">Back to Admin Dashboard</a></p>
</div></body></html>"""


@app.route("/admin/exam/<exam_id>/recordings")
def admin_exam_recordings(exam_id):
    """Pick a student, get ONLY that student's recording for this subject."""
    if "admin_id" not in session:
        return redirect(url_for("admin_login"))
    entries, subject_name, subject_code = [], "", ""
    try:
        entries, subject_name, subject_code = _recording_entries_for_subject(exam_id)
    except Exception as e:
        print("Admin recording lookup warning:", e)
    seen, students = set(), []
    for e in sorted(entries, key=lambda x: str(x["student_name"]).lower()):
        if e["student_id"] and e["student_id"] not in seen:
            seen.add(e["student_id"])
            students.append(e)
    selected = (request.args.get("student_id") or "").strip()
    shown = [e for e in entries if selected and e["student_id"] == selected]
    return render_template_string(
        ADMIN_RECORDINGS_PAGE, subject_name=subject_name, subject_code=subject_code,
        students=students, selected=selected, shown=shown,
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
        cloud_url = _cloudinary_recording_url(safe_name, download=True)
        return redirect(cloud_url) if cloud_url else ("Recording not found", 404)

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
        cloud_url = _cloudinary_recording_url(safe_name)
        return redirect(cloud_url) if cloud_url else ("Recording not found", 404)

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

LIVE_ACTIVE_WINDOW_SECONDS = 20

_PULL_CACHE = {"t": 0.0, "data": []}
_PULL_LOCK = threading.Lock()


def _pull_student_live_sessions():
    """Ask the student server who is live right now. Complements the pushes
    the student makes, so a dropped heartbeat never hides a student."""
    if not STUDENT_SIGNAL_BASE_URL or not LIVE_SYNC_TOKEN:
        return []
    now = time.time()
    with _PULL_LOCK:
        if now - _PULL_CACHE["t"] < 1.5:
            return list(_PULL_CACHE["data"])
        _PULL_CACHE["t"] = now          # also throttles retries after a failure
        try:
            r = requests.get(
                f"{STUDENT_SIGNAL_BASE_URL}/internal/live-sessions",
                headers={"X-ExamGuard-Sync-Token": LIVE_SYNC_TOKEN},
                timeout=(2.5, 5), verify=STUDENT_SIGNAL_VERIFY_SSL,
            )
            data = []
            if r.ok:
                for s in (r.json().get("sessions") or []):
                    try: s["last_seen"] = now - float(s.get("age", 0) or 0)
                    except Exception: s["last_seen"] = now
                    data.append(s)
            _PULL_CACHE["data"] = data
        except Exception as exc:
            print("[LIVE PULL] sessions:", exc)
            _PULL_CACHE["data"] = []
        return list(_PULL_CACHE["data"])


def get_active_live_sessions():
    """Exactly one active session per student (pushed files + pulled list)."""
    now = time.time(); newest = {}

    def consider(data):
        sid = str(data.get("student_id", "")).strip()
        try: seen = float(data.get("last_seen", 0) or 0)
        except Exception: return
        if not sid or now - seen > LIVE_ACTIVE_WINDOW_SECONDS:
            return
        if sid not in newest or seen >= float(newest[sid].get("last_seen", 0) or 0):
            # keep the richest data for fields the newer record may lack
            merged = dict(newest.get(sid, {})); merged.update({k: v for k, v in data.items() if v not in (None, "")} )
            merged["last_seen"] = seen
            newest[sid] = merged

    if os.path.isdir(LIVE_FRAMES_FOLDER):
        for filename in os.listdir(LIVE_FRAMES_FOLDER):
            if not filename.endswith(".json") or filename.endswith(".uploading"): continue
            try:
                with open(os.path.join(LIVE_FRAMES_FOLDER, filename), "r", encoding="utf-8") as fh:
                    consider(json.load(fh))
            except Exception:
                continue
    for s in _pull_student_live_sessions():
        consider(s)
    result = list(newest.values()); result.sort(key=lambda x: str(x.get("student_name", "")))
    return result


LIVE_PAGE_HTML = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Live Exam Monitoring</title>
<style>
  :root{--bg:#0a0e1a;--card:#141a2c;--line:rgba(255,255,255,.1);--text:#f1f0f7;--muted:#a7a2bd;--accent:#9d85ff;--ok:#4ade80;--bad:#f87171;--warn:#fbbf24}
  *{box-sizing:border-box}
  body{font-family:'Segoe UI',Arial,sans-serif;background:var(--bg);color:var(--text);padding:26px;margin:0}
  a.back{color:var(--accent);text-decoration:none;font-size:13.5px}
  h1{font-size:22px;margin:14px 0 4px}.sub{color:var(--muted);font-size:13.5px;margin-bottom:16px}
  #voicebar{display:flex;gap:10px;align-items:center;flex-wrap:wrap;background:var(--card);border:1px solid rgba(157,133,255,.3);border-radius:12px;padding:14px 16px;margin:14px 0 20px}
  button{font-family:inherit}
  #voiceBtn{background:var(--accent);color:#fff;border:0;padding:11px 18px;border-radius:8px;font-weight:700;cursor:pointer}
  #voiceBtn.on{background:var(--ok);color:#07130b}
  #audioBtn{background:#19a974;color:#fff;border:0;padding:11px 18px;border-radius:8px;font-weight:700;cursor:pointer}
  #audioBtn.on{background:#0f766e}
  .muted{color:var(--muted);font-size:12.5px}.dot{width:9px;height:9px;border-radius:50%;background:var(--ok);display:inline-block;margin-right:6px}
  #count{margin-left:auto;font-weight:700;font-size:13px;color:var(--muted)}
  #grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(300px,1fr));gap:16px}
  .card{background:var(--card);border:1px solid var(--line);border-radius:12px;overflow:hidden;cursor:pointer;transition:border-color .2s}
  .card:hover{border-color:var(--accent)}
  .card.alert{border-color:var(--bad);box-shadow:0 0 0 1px rgba(248,113,113,.4)}
  .shot{position:relative;background:#000;aspect-ratio:4/3}
  .shot img,.shot video{position:absolute;inset:0;width:100%;height:100%;object-fit:cover;display:block;background:#000}
  .shot video{opacity:0;transition:opacity .25s}
  .shot.vid video{opacity:1}
  .badge{position:absolute;left:8px;top:8px;background:rgba(0,0,0,.68);padding:4px 8px;border-radius:6px;font:600 11px monospace;z-index:3}
  .wchip{position:absolute;right:8px;top:8px;z-index:3;background:rgba(0,0,0,.68);padding:4px 9px;border-radius:12px;font:700 11px 'Segoe UI',Arial;color:var(--ok)}
  .wchip.w1{color:var(--warn)}.wchip.w2{color:#fb923c}.wchip.w3{color:var(--bad)}
  .banner{position:absolute;left:0;right:0;bottom:0;z-index:3;background:rgba(127,29,29,.92);color:#fff;font:600 12px 'Segoe UI',Arial;padding:6px 10px;display:none}
  .card.alert .banner{display:block}
  .meta{padding:11px 14px}.name{font-weight:600;font-size:14px}.exam{color:#9891ab;font-size:11.5px;margin-top:2px;font-family:monospace}
  .status{font-size:12px;margin-top:6px;padding:2px 9px;border-radius:12px;display:inline-block}
  .s-ok{background:#143322;color:var(--ok);border:1px solid #245c3a}.s-bad{background:#32191d;color:var(--bad);border:1px solid #5c2a2a}.s-end{background:#2a2a35;color:#cbd5e1;border:1px solid #475569}
  .last{color:#cbd5e1;font-size:11.5px;margin-top:6px;min-height:15px;overflow-wrap:anywhere}
  #empty{color:#9891ab;padding:60px 0;text-align:center}
</style>
</head>
<body>
  <a class="back" href="/admin/dashboard">&larr; Back to Admin Dashboard</a>
  <h1>Live Exam Monitoring</h1>
  <div class="sub">One live card per student currently taking an exam &mdash; camera, voice and malpractice alerts.</div>

  <div id="voicebar">
    <button id="voiceBtn" type="button">&#127897; Start Speaking to Students</button>
    <button id="audioBtn" type="button">&#128266; Enable Student Audio</button>
    <span id="voiceStatus" class="muted"><span class="dot"></span>Voice broadcast is off</span>
    <span id="count">0 students live</span>
  </div>

  <div id="grid"></div>
  <div id="empty" style="display:none">No students are currently taking an exam.</div>

<script>
(function(){
  const ICE = __ICE_SERVERS_JSON__;
  const grid = document.getElementById('grid');
  const empty = document.getElementById('empty');
  const countEl = document.getElementById('count');
  const voiceBtn = document.getElementById('voiceBtn');
  const audioBtn = document.getElementById('audioBtn');
  const voiceStatus = document.getElementById('voiceStatus');

  const cards = new Map();            // id -> state
  const voicePCs = new Map();         // id -> RTCPeerConnection
  let studentAudioOn = false, voiceRunning = false, adminMic = null, refreshBusy = false;

  const key = id => String(id).replace(/[^A-Za-z0-9_-]/g,'_');
  const sleep = ms => new Promise(r => setTimeout(r, ms));
  function setVoiceStatus(t){ voiceStatus.innerHTML = '<span class="dot"></span>' + t; }

  function waitIce(pc, ms){
    if (pc.iceGatheringState === 'complete') return Promise.resolve();
    return new Promise(res => {
      const done = () => { clearTimeout(t); pc.removeEventListener('icegatheringstatechange', chk); res(); };
      const chk = () => { if (pc.iceGatheringState === 'complete') done(); };
      const t = setTimeout(done, ms || 4000);
      pc.addEventListener('icegatheringstatechange', chk);
    });
  }

  // ------------------------------------------------------------ cards
  function makeCard(s){
    const id = String(s.student_id || '').trim();
    const el = document.createElement('div');
    el.className = 'card'; el.id = 'card-' + key(id);
    el.onclick = () => { location.href = '/admin/live/' + encodeURIComponent(id); };
    el.innerHTML =
      '<div class="shot">' +
        '<img alt="" decoding="async">' +
        '<video autoplay playsinline muted></video>' +
        '<div class="badge">CONNECTING&hellip;</div>' +
        '<div class="wchip">Warnings 0/3</div>' +
        '<div class="banner"></div>' +
      '</div>' +
      '<div class="meta"><div class="name"></div><div class="exam"></div>' +
      '<span class="status s-ok">Normal</span><div class="last"></div></div>';
    grid.appendChild(el);
    const st = {
      id, el, exam: s.exam_id || '', img: el.querySelector('img'), video: el.querySelector('video'),
      shot: el.querySelector('.shot'), badge: el.querySelector('.badge'), chip: el.querySelector('.wchip'),
      banner: el.querySelector('.banner'), statusEl: el.querySelector('.status'), lastEl: el.querySelector('.last'),
      pc: null, busy: false, vidSince: 0, lastTime: -1, lastAdv: Date.now(), frameBusy: false, retryAt: 0, audioBusy: false,
      connectStarted: 0
    };
    cards.set(id, st);
    startVideoPeer(st);
    return st;
  }

  function updateCard(s){
    const id = String(s.student_id || '').trim(); if (!id) return;
    const st = cards.get(id) || makeCard(s);
    st.exam = s.exam_id || st.exam;
    st.el.querySelector('.name').textContent = s.student_name || id;
    st.el.querySelector('.exam').textContent = s.exam_id || '';
    const n = Math.max(0, parseInt(s.violation_count || 0, 10));
    st.chip.textContent = 'Warnings ' + Math.min(n, 3) + '/3';
    st.chip.className = 'wchip' + (n >= 1 ? ' w' + Math.min(n, 3) : '');
    const warn = !!s.warning;
    const ended = !!s.terminated;
    st.el.classList.toggle('alert', warn);
    st.banner.textContent = warn ? ('⚠ ' + (s.warning_message || 'Malpractice detected')) : '';
    st.statusEl.className = 'status ' + (ended ? 's-end' : (warn ? 's-bad' : 's-ok'));
    st.statusEl.textContent = ended ? 'Exam ended' : (warn ? (s.warning_message || 'Warning') : 'Normal');
    st.lastEl.textContent = s.last_violation ? ('Last: ' + s.last_violation) : '';
  }

  function removeCard(id){
    const st = cards.get(id); if (!st) return;
    stopVideoPeer(st);
    st.el.remove(); cards.delete(id);
  }

  async function refreshGrid(){
    if (refreshBusy) return; refreshBusy = true;
    try {
      const res = await fetch('/admin/live-status', {cache: 'no-store'});
      if (!res.ok) throw new Error('HTTP ' + res.status);
      const raw = await res.json();
      const by = new Map();
      for (const s of raw) { const id = String(s.student_id || '').trim(); if (id) by.set(id, s); }
      for (const s of by.values()) updateCard(s);
      for (const id of Array.from(cards.keys())) if (!by.has(id)) removeCard(id);
      empty.style.display = by.size ? 'none' : 'block';
      countEl.textContent = by.size + ' student' + (by.size === 1 ? '' : 's') + ' live';
    } catch (e) { console.error('[LIVE GRID]', e); }
    finally { refreshBusy = false; }
  }

  // --------------------------------------------- JPEG fallback (always on)
  function refreshFrames(){
    cards.forEach(st => {
      if (st.frameBusy) return;
      st.frameBusy = true;
      const im = new Image();
      im.onload = () => { st.img.src = im.src; st.frameBusy = false; if (!st.shot.classList.contains('vid')) st.badge.textContent = '● LIVE (snapshot)'; };
      im.onerror = () => { st.frameBusy = false; };
      im.src = '/admin/live-frame/' + encodeURIComponent(st.id) + '?t=' + Date.now();
    });
  }

  // ------------------------------------------------ WebRTC camera + audio
  function stopVideoPeer(st){
    if (st.pc) { try { st.pc.close(); } catch (e) {} st.pc = null; }
    st.shot.classList.remove('vid'); st.vidSince = 0;
    try { st.video.srcObject = null; } catch (e) {}
    fetch('/admin/video/stop/' + encodeURIComponent(st.id), {method: 'POST'}).catch(() => {});
  }

  async function startVideoPeer(st){
    if (st.busy || !cards.has(st.id)) return;
    if (Date.now() < st.retryAt) return;
    st.busy = true; st.connectStarted = Date.now();
    try {
      if (st.pc) { try { st.pc.close(); } catch (e) {} st.pc = null; }
      const pc = new RTCPeerConnection({iceServers: ICE});
      st.pc = pc;
      pc.addTransceiver('video', {direction: 'recvonly'});
      pc.addTransceiver('audio', {direction: 'recvonly'});
      const remote = new MediaStream();
      pc.ontrack = e => {
        if (e.track && !remote.getTracks().some(t => t.id === e.track.id)) remote.addTrack(e.track);
        st.video.srcObject = remote;
        st.video.muted = !studentAudioOn;
        st.video.volume = 1.0;
        st.video.play().catch(() => {});
      };
      pc.onconnectionstatechange = () => {
        if (st.pc !== pc) return;
        if (['failed', 'closed'].includes(pc.connectionState)) {
          st.shot.classList.remove('vid');
          st.retryAt = Date.now() + 1500;
          try { pc.close(); } catch (e) {}
          st.pc = null;
        }
      };
      const offer = await pc.createOffer();
      await pc.setLocalDescription(offer);
      await waitIce(pc, 4000);
      const r = await fetch('/admin/video/offer', {
        method: 'POST', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({student_id: st.id, exam_id: st.exam, offer: pc.localDescription})
      });
      const d = await r.json().catch(() => ({}));
      if (!r.ok || !d.success) throw new Error(d.error || ('offer HTTP ' + r.status));
      pollAnswer(st, pc);
    } catch (e) {
      console.debug('[LIVE VIDEO]', st.id, e);
      if (st.pc) { try { st.pc.close(); } catch (_) {} st.pc = null; }
      st.retryAt = Date.now() + 3000;
    } finally { st.busy = false; }
  }

  async function pollAnswer(st, pc){
    for (let n = 0; n < 45; n++) {
      if (st.pc !== pc) return;
      try {
        const r = await fetch('/admin/video/answer/' + encodeURIComponent(st.id) + '?t=' + Date.now(), {cache: 'no-store'});
        if (r.ok) {
          const d = await r.json();
          if (d.success && d.answer) { await pc.setRemoteDescription(new RTCSessionDescription(d.answer)); return; }
        }
      } catch (e) {}
      await sleep(350);
    }
    if (st.pc === pc && pc.connectionState !== 'connected') {
      try { pc.close(); } catch (e) {} st.pc = null; st.retryAt = Date.now() + 1500;
    }
  }

  // Supervises every card: detects frozen/never-connected video and retries.
  function superviseVideo(){
    const now = Date.now();
    cards.forEach(st => {
      const v = st.video;
      const playing = v.srcObject && v.videoWidth > 0 && !v.paused && v.readyState >= 2;
      if (playing) {
        if (v.currentTime !== st.lastTime) { st.lastTime = v.currentTime; st.lastAdv = now; }
        if (now - st.lastAdv > 6000) { // frozen
          st.shot.classList.remove('vid');
          if (st.pc) { try { st.pc.close(); } catch (e) {} st.pc = null; }
          st.retryAt = 0;
        } else {
          st.shot.classList.add('vid');
          const hasA = v.srcObject.getAudioTracks().length > 0;
          st.badge.textContent = hasA ? '● LIVE VIDEO + AUDIO' : '● LIVE VIDEO';
        }
      } else {
        st.shot.classList.remove('vid');
        if (!st.pc && !st.busy) startVideoPeer(st);
        else if (st.pc && now - st.connectStarted > 15000 && st.pc.connectionState !== 'connected') {
          try { st.pc.close(); } catch (e) {} st.pc = null; st.retryAt = 0;
        }
      }
    });
  }

  // ---------------- student audio fallback (when WebRTC audio is absent)
  async function audioFallback(){
    if (!studentAudioOn) return;
    for (const st of cards.values()) {
      if (st.shot.classList.contains('vid') || st.audioBusy) continue;
      st.audioBusy = true;
      try {
        const r = await fetch('/admin/live-audio/' + encodeURIComponent(st.id) + '?t=' + Date.now(), {cache: 'no-store'});
        if (r.status === 200) {
          const blob = await r.blob();
          if (blob.size > 256) {
            const a = new Audio(URL.createObjectURL(blob));
            a.onended = () => URL.revokeObjectURL(a.src);
            await a.play().catch(() => {});
          }
        }
      } catch (e) {}
      st.audioBusy = false;
    }
  }

  async function enableStudentAudio(){
    studentAudioOn = true;
    audioBtn.textContent = '🔊 Student Audio ON'; audioBtn.classList.add('on');
    for (const st of cards.values()) { st.video.muted = false; st.video.volume = 1; try { await st.video.play(); } catch (e) {} }
  }

  // --------------------------------------- admin -> students voice
  async function startVoiceStudent(s){
    const id = String(s.student_id || ''), exam = String(s.exam_id || '');
    if (!id || !exam || voicePCs.has(id) || !adminMic) return;
    const pc = new RTCPeerConnection({iceServers: ICE});
    pc._created = Date.now();
    voicePCs.set(id, pc);
    adminMic.getTracks().forEach(t => pc.addTrack(t, adminMic));
    pc.onconnectionstatechange = () => {
      if (['failed', 'closed'].includes(pc.connectionState) && voicePCs.get(id) === pc) {
        voicePCs.delete(id); try { pc.close(); } catch (e) {}
      }
    };
    try {
      const offer = await pc.createOffer();
      await pc.setLocalDescription(offer);
      await waitIce(pc, 4000);
      const r = await fetch('/admin/voice/offer', {
        method: 'POST', headers: {'Content-Type': 'application/json'},
        body: JSON.stringify({student_id: id, exam_id: exam, offer: pc.localDescription})
      });
      const d = await r.json().catch(() => ({}));
      if (!r.ok || !d.success) throw new Error(d.error || 'voice offer failed');
    } catch (e) {
      try { pc.close(); } catch (_) {}
      if (voicePCs.get(id) === pc) voicePCs.delete(id);
    }
  }

  async function pollVoiceAnswers(){
    for (const [id, pc] of Array.from(voicePCs.entries())) {
      if (pc.currentRemoteDescription) continue;
      if (Date.now() - pc._created > 25000) { // student never answered: retry fresh
        try { pc.close(); } catch (e) {} voicePCs.delete(id);
        fetch('/admin/voice/stop/' + encodeURIComponent(id), {method: 'POST'}).catch(() => {});
        continue;
      }
      try {
        const r = await fetch('/admin/voice/answer/' + encodeURIComponent(id) + '?t=' + Date.now(), {cache: 'no-store'});
        const d = await r.json();
        if (d.success && d.answer && !pc.currentRemoteDescription) await pc.setRemoteDescription(new RTCSessionDescription(d.answer));
      } catch (e) {}
    }
  }

  async function syncVoiceStudents(){
    if (!voiceRunning) return;
    try {
      const res = await fetch('/admin/live-status', {cache: 'no-store'});
      const list = await res.json();
      const ids = new Set(list.map(s => String(s.student_id)));
      for (const [id, pc] of Array.from(voicePCs.entries())) if (!ids.has(id)) { try { pc.close(); } catch (e) {} voicePCs.delete(id); }
      await Promise.all(list.map(startVoiceStudent));
      let connected = 0; voicePCs.forEach(pc => { if (pc.connectionState === 'connected') connected++; });
      setVoiceStatus('Broadcast ON — ' + connected + ' of ' + list.length + ' student' + (list.length === 1 ? '' : 's') + ' hearing you');
    } catch (e) { setVoiceStatus('Broadcast ON — waiting for students'); }
  }

  async function stopVoice(){
    voiceRunning = false;
    for (const [id, pc] of Array.from(voicePCs.entries())) {
      try { pc.close(); } catch (e) {}
      fetch('/admin/voice/stop/' + encodeURIComponent(id), {method: 'POST'}).catch(() => {});
    }
    voicePCs.clear();
    if (adminMic) adminMic.getTracks().forEach(t => t.stop());
    adminMic = null;
    voiceBtn.innerHTML = '&#127897; Start Speaking to Students'; voiceBtn.classList.remove('on');
    setVoiceStatus('Voice broadcast is off');
  }

  async function startVoice(){
    try {
      adminMic = await navigator.mediaDevices.getUserMedia({audio: {echoCancellation: true, noiseSuppression: true, autoGainControl: true}, video: false});
      voiceRunning = true;
      voiceBtn.innerHTML = '&#128308; Stop Speaking'; voiceBtn.classList.add('on');
      await syncVoiceStudents();
    } catch (e) { alert('Microphone access was not granted.'); await stopVoice(); }
  }

  audioBtn.addEventListener('click', enableStudentAudio);
  voiceBtn.addEventListener('click', () => voiceRunning ? stopVoice() : startVoice());
  setInterval(refreshGrid, 1500);
  setInterval(refreshFrames, 1200);
  setInterval(superviseVideo, 1500);
  setInterval(syncVoiceStudents, 2500);
  setInterval(pollVoiceAnswers, 900);
  setInterval(audioFallback, 3000);
  refreshGrid();
  window.addEventListener('beforeunload', () => {
    voicePCs.forEach(pc => { try { pc.close(); } catch (e) {} });
    cards.forEach(st => { if (st.pc) try { st.pc.close(); } catch (e) {} });
  });
})();
</script>
</body>
</html>
"""


@app.route("/admin/live")
def admin_live():
    if "admin_id" not in session:
        return redirect(url_for("admin_login"))
    html = LIVE_PAGE_HTML.replace("__ICE_SERVERS_JSON__", json.dumps(_ice_servers()))
    resp = app.response_class(html, mimetype="text/html")
    resp.headers["Cache-Control"] = "no-store"
    return resp


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
    if not student_base:
        student_base=STUDENT_SIGNAL_BASE_URL

    try:
        if os.path.isfile(local_path) and time.time() - os.path.getmtime(local_path) < 3.5:
            response=send_from_directory(LIVE_FRAMES_FOLDER,f"{safe_id}.jpg",mimetype="image/jpeg")
            response.headers["Cache-Control"]="no-store, no-cache, must-revalidate, max-age=0"
            return response
    except OSError:
        pass

    # PRIMARY path for two-computer deployments: pull the newest JPEG
    # directly from the student's Flask server. This avoids relying on a
    # shared filesystem and avoids stale admin-side JPEGs.
    if student_base and LIVE_SYNC_TOKEN:
        try:
            r=requests.get(
                f"{student_base}/internal/live-frame/{safe_id}",
                headers={"X-ExamGuard-Sync-Token":LIVE_SYNC_TOKEN},
                timeout=(3,6),
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
                # Render terminates HTTPS at its proxy. A Flask-generated
                # request.url_root can otherwise be http://, which can break
                # POST-based WebRTC signaling after an HTTPS redirect.
                if base.startswith("http://") and (
                    ".onrender.com" in base.lower()
                    or os.environ.get("RENDER", "").strip().lower() == "true"
                ):
                    base = "https://" + base[len("http://"):]
                return base
            break
    base = STUDENT_SIGNAL_BASE_URL.rstrip("/")
    if base.startswith("http://") and ".onrender.com" in base.lower():
        base = "https://" + base[len("http://"):]
    return base


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


def _bootstrap_for_wsgi():
    """gunicorn imports this module instead of running __main__, so do the
    one-time database/column setup and the Cloudinary sweeper here too."""
    for fn in (initialize_database, ensure_recording_column, ensure_exam_status_column,
               ensure_result_student_detail_columns, ensure_exam_timing_columns,
               ensure_exam_duration_column, ensure_violations_sheet, _migrate_public_exams_once):
        try:
            fn()
        except Exception as exc:
            print("[BOOT]", getattr(fn, "__name__", fn), "skipped:", exc)
    _start_cloud_sweeper()
    try:
        _start_exam_push_thread()
        _EXAM_PUSH_EVENT.set()
    except Exception as exc:
        print("[BOOT] exam push skipped:", exc)


if __name__ != "__main__":
    _bootstrap_for_wsgi()


if __name__ == "__main__":

    _start_cloud_sweeper()
    _start_exam_push_thread()
    _EXAM_PUSH_EVENT.set()
    initialize_database()
    ensure_recording_column()
    ensure_exam_status_column()
    ensure_result_student_detail_columns()
    ensure_exam_timing_columns()
    ensure_exam_duration_column()
    ensure_violations_sheet()
    try:
        _migrate_public_exams_once()
    except Exception as exc:
        print("[MIGRATE] skipped:", exc)

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
