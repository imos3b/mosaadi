#!/usr/bin/env python3
"""
بوابة مساعدي: توقف قدّام Ollama و Glances و macmon (والـ NAS و Uptime Kuma و SearXNG لو تبي)،
وكل جهاز يتصل يحتاج مفتاح خاص فيه، وكل شخص له صلاحيات.

بدون أي مكتبات خارجية (Python 3.9 أو أحدث، اللي يجي مع الماك).

الأوامر:
  python3 gateway.py serve            يشغّل البوابة (التركيب يسويه تلقائياً)
  python3 gateway.py pair             رمز ربط جديد لجوالك (يصلح 10 دقايق)
  python3 gateway.py users            يعرض المستخدمين
  python3 gateway.py disable <الاسم>   يوقف شخص
  python3 gateway.py enable <الاسم>    يرجّع شخص
  python3 gateway.py review [أيام|off] حساب مؤقت لمراجعة Apple
  python3 gateway.py version          نسخة البوابة
  python3 gateway.py brief [send]     ملخص الصباح الحين (send = يرسله تنبيه)
  python3 gateway.py merge            يجمع أجهزتك (المالك) في حساب واحد: نفس المحادثات والذاكرة
  python3 gateway.py push-setup <ملف.p8> <Key ID> <Team ID>   تنبيهات الآيفون (مرة وحدة)
  python3 gateway.py push-test        يرسل تنبيه تجربة لأجهزتك
  python3 gateway.py wake-setup <عنوان>  تجهيز تصحية الماك من الـ NAS (مثل http://100.71.65.118:9009)
"""

VERSION = "1.9.0"
# التحديث بضغطة من التطبيق: البوابة تنزّل نفسها من هنا (غيّره في config.json: "update_url")
DEFAULT_UPDATE_URL = "https://imos3b.github.io/mosaadi/gateway/gateway.py"

import base64
import hashlib
import hmac
import html as htmllib
import io
import http.client
import json
import os
import re
import secrets
import shutil
import subprocess
import sys
import threading
import time
import urllib.parse
import urllib.request
import zipfile
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HOME = os.path.expanduser("~/Library/Application Support/PrivateAI-Gateway")
BACKUPS = os.path.join(HOME, "backups")
IMAGES = os.path.join(HOME, "images")
MAX_IMAGE = 20 * 1024 * 1024
MAX_BACKUP = 200 * 1024 * 1024
MAX_MEMORY = 4000
CONFIG = os.path.join(HOME, "config.json")
USERS = os.path.join(HOME, "users.json")
PAIR = os.path.join(HOME, "pair.json")

LOCK = threading.RLock()  # RLock: نفس الخيط يقدر ياخذه مرتين

# الصلاحيات: كل خدمة لها صلاحية، والمالك عنده كل شي
PERMS = ["chat", "images", "search", "servers", "mac", "nas", "choose_model", "claude"]
SERVICE_PERM = {"ollama": "chat", "glances": "mac", "macmon": "mac", "nas": "nas", "kuma": "servers", "searx": "search",
                "claude": "claude"}
CLAUDE_DEFAULT_LIMIT = 10  # رسائل Claude باليوم لكل شخص (لما يستخدم مفتاح المالك)

# أوامر Ollama المسموحة لغير المالك (القراءة والمحادثة بس، ما يقدر يحذف أو ينزّل موديلات)
OLLAMA_MEMBER_PATHS = {"/", "/api/tags", "/api/chat", "/api/generate", "/api/show", "/api/ps", "/api/version"}


# ─────────── الملفات ───────────

def load(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (FileNotFoundError, ValueError):
        return default


def save(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)
    os.chmod(tmp, 0o600)
    os.replace(tmp, path)


def token_hash(token):
    return hashlib.sha256(token.encode()).hexdigest()


def new_token():
    return "pa_" + secrets.token_urlsafe(24)


def now():
    return int(time.time())


def find_user(token):
    if not token:
        return None
    h = token_hash(token)
    for u in load(USERS, {"users": []})["users"]:
        # extra_tokens: حساب المراجعة يقدر يكون على أكثر من جهاز
        if any(hmac.compare_digest(t, h) for t in [u.get("token_hash", "")] + u.get("extra_tokens", [])):
            return u
    return None


def touch(user_id):
    """يسجّل آخر استخدام (مرة بالدقيقة كحد أقصى عشان ما نكتب الملف مع كل طلب)."""
    with LOCK:
        data = load(USERS, {"users": []})
        for u in data["users"]:
            if u["id"] == user_id and now() - u.get("last_used", 0) > 60:
                u["last_used"] = now()
                save(USERS, data)
                return


def today():
    return time.strftime("%Y-%m-%d")


def claude_used(u):
    usage = u.get("claude_usage") or {}
    return usage.get("count", 0) if usage.get("day") == today() else 0


def public(u):
    """اللي نرجّعه للتطبيق: بدون المفتاح ومفتاح Claude الخاص."""
    out = {k: v for k, v in u.items() if k not in ("token_hash", "claude_key", "claude_usage", "extra_tokens", "device_id", "memory", "backup_at", "learned", "push", "devices")}
    out.setdefault("paired", True)
    out["claude_limit"] = u.get("claude_limit", CLAUDE_DEFAULT_LIMIT)
    out["claude_used"] = claude_used(u)
    out["own_claude_key"] = bool(u.get("claude_key"))
    return out


def has(u, perm):
    return u["role"] == "owner" or bool(u.get("perms", {}).get(perm))


def model_allowed(u, model):
    if u["role"] == "owner":
        return True
    models = u.get("models", [])
    return "*" in models or model in models or model.split(":")[0] in models


# ─────────── الربط بالجوال ───────────

def create_pair_code(role="owner", user_id=None, link=False):
    """link=True: جهاز ثاني لنفس الشخص (نفس الحساب: المحادثات والذاكرة والاسم مشتركة)."""
    code = "".join(secrets.choice("0123456789") for _ in range(6))
    with LOCK:
        data = load(PAIR, {"codes": []})
        data["codes"] = [c for c in data["codes"] if c["expires"] > now()]
        data["codes"].append({"code": code, "role": role, "user_id": user_id, "link": link, "expires": now() + 600})
        save(PAIR, data)
        if user_id and not link:
            users = load(USERS, {"users": []})
            for u in users["users"]:
                if u["id"] == user_id:
                    u["invite_expires"] = now() + 600
            save(USERS, users)
    return code


FAILED = {}   # عنوان ← {"count", "until"}: 5 محاولات غلط من نفس العنوان = قفل 10 دقايق
FAILED_ALL = {"times": []}   # حماية إضافية: 30 محاولة غلط من أي مكان خلال 10 دقايق = قفل للكل


def redeem(code, device, ip="", device_id=""):
    """يحوّل رمز الربط لمفتاح دائم."""
    with LOCK:
        f = FAILED.setdefault(ip, {"count": 0, "until": 0})
        FAILED_ALL["times"] = [t for t in FAILED_ALL["times"] if t > now() - 600]
        if f["until"] > now() or len(FAILED_ALL["times"]) >= 30:
            return None, "محاولات كثيرة غلط. انتظر 10 دقايق."
        pairs = load(PAIR, {"codes": []})
        match = next((c for c in pairs["codes"] if c["code"] == code and c["expires"] > now()), None)
        if not match:
            f["count"] += 1
            FAILED_ALL["times"].append(now())
            if f["count"] >= 5:
                f.update(count=0, until=now() + 600)
            return None, "الرمز غلط أو انتهى. سوّ رمز جديد بأمر: python3 gateway.py pair"
        f["count"] = 0
        if not match.get("reusable"):
            pairs["codes"] = [c for c in pairs["codes"] if c is not match]
            save(PAIR, pairs)

        token = new_token()
        data = load(USERS, {"users": []})
        if match.get("user_id") and match.get("link"):
            # جهاز ثاني لك: نفس الحساب بمفتاح جديد
            user = next((u for u in data["users"] if u["id"] == match["user_id"]), None)
            if not user:
                return None, "المستخدم انحذف."
            user["extra_tokens"] = (user.get("extra_tokens", []) + [token_hash(token)])[-10:]
            user["devices"] = (user.get("devices", []) + [{"name": device, "at": now()}])[-10:]
            user["last_used"] = now()
        elif match.get("user_id"):
            user = next((u for u in data["users"] if u["id"] == match["user_id"]), None)
            if not user:
                return None, "المستخدم انحذف."
            if match.get("reusable"):
                user["extra_tokens"] = (user.get("extra_tokens", []) + [token_hash(token)])[-10:]
            else:
                user["token_hash"] = token_hash(token)
            user["device"] = device
            if device_id:
                user["device_id"] = device_id
            user["paired"] = True
            user["invite_expires"] = 0
            user["last_used"] = now()
        elif device_id and any(u.get("device_id") == device_id and u["role"] == "owner" for u in data["users"]):
            user = next(u for u in data["users"] if u.get("device_id") == device_id and u["role"] == "owner")
            user["token_hash"] = token_hash(token)
            user["device"] = device
            user["disabled"] = False
            user["last_used"] = now()
        else:
            user = {
                "id": secrets.token_hex(4), "name": device or "جوالي", "role": "owner", "device_id": device_id,
                "token_hash": token_hash(token), "perms": {p: True for p in PERMS}, "models": ["*"],
                "disabled": False, "created": now(), "last_used": now(), "device": device, "paired": True,
            }
            data["users"].append(user)
        save(USERS, data)
        return {"token": token, "user": public(user)}, None


# ─────────── البوابة ───────────

class Gateway(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "PrivateAI-Gateway/1"

    def handle(self):
        try:
            super().handle()
        except (ConnectionResetError, BrokenPipeError, TimeoutError):
            pass  # الجوال قفل الاتصال: عادي

    def log_message(self, fmt, *args):  # سجل مختصر بدون المفاتيح
        sys.stderr.write("%s %s\n" % (time.strftime("%H:%M:%S"), fmt % args))

    # ── ردود جاهزة ──
    def reply(self, code, obj):
        body = json.dumps(obj, ensure_ascii=False).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def error(self, code, message):
        # نفس شكل أخطاء Ollama عشان التطبيق يعرضها مثل ما هي
        self.reply(code, {"error": message})

    def body(self):
        n = int(self.headers.get("Content-Length") or 0)
        return self.rfile.read(n) if n else b""

    def user(self):
        auth = self.headers.get("Authorization", "")
        token = auth[7:].strip() if auth.lower().startswith("bearer ") else ""
        u = find_user(token)
        if not u:
            self.error(401, "مفتاح البوابة غير صحيح. اربط التطبيق من جديد من الإعدادات ← البوابة.")
            return None
        if u.get("disabled"):
            self.error(403, "وصولك للمساعد موقوف.")
            return None
        touch(u["id"])
        return u

    # ── التوجيه ──
    def do_GET(self):
        self.route("GET")

    def do_POST(self):
        self.route("POST")

    def do_PATCH(self):
        self.route("PATCH")

    def do_DELETE(self):
        self.route("DELETE")

    def do_HEAD(self):
        self.route("HEAD")

    def do_PUT(self):
        self.route("PUT")

    def route(self, method):
        try:
            path = urllib.parse.urlsplit(self.path).path
            if path == "/gateway/pair" and method == "POST":
                return self.pair()
            if path == "/" and method in ("GET", "HEAD"):
                return self.reply(200, {"gateway": "PrivateAI", "ok": True})

            u = self.user()
            if not u:
                return
            if path == "/gateway/me":
                return self.me(u)
            if path == "/gateway/settings":
                return self.settings(u, method)
            if path == "/gateway/me/memory":
                return self.memory(u, method)
            if path == "/gateway/me/learn" and method == "POST":
                return self.learn(u)
            if path == "/gateway/me/backup":
                return self.backup(u, method)
            if path.startswith("/gateway/me/images/"):
                return self.image(u, method, path.rsplit("/", 1)[-1])
            if path == "/gateway/me/name" and method == "POST":
                return self.set_name(u)
            if path == "/gateway/me/push" and method == "POST":
                return self.register_push(u)
            if path == "/gateway/brief":
                return self.brief_api(u, method)
            if path == "/gateway/studies" and method == "GET":
                return self.studies_api(u)
            if path == "/gateway/extract" and method == "POST":
                return self.extract_api(u)
            if path.startswith("/gateway/jobs/"):
                return self.job_api(u, method, path)
            if path == "/gateway/pair-code" and method == "POST":
                if u["role"] != "owner":
                    return self.error(403, "للمالك بس.")
                # جهاز ثاني لك: ينربط بنفس حسابك (نفس المحادثات والذاكرة)
                return self.reply(200, {"code": create_pair_code("owner", u["id"], link=True), "expires_in": 600})
            if path == "/gateway/ollama-lock":
                if u["role"] != "owner":
                    return self.error(403, "للمالك بس.")
                if method == "POST":
                    req = json.loads(self.body() or b"{}")
                    err = set_ollama_lock(bool(req.get("locked")))
                    if err:
                        return self.error(500, err)
                return self.reply(200, {"locked": ollama_locked()})
            if path.startswith("/gateway/users"):
                return self.users(u, method, path)
            if path == "/gateway/version":
                return self.reply(200, {"version": VERSION})
            if path == "/gateway/update":
                return self.update(u, method)
            if path == "/gateway/disk":
                if u["role"] != "owner":
                    return self.error(403, "للمالك بس.")
                du = shutil.disk_usage(os.path.expanduser("~"))
                return self.reply(200, {"total": du.total, "free": du.free})
            if path == "/gateway/claude":
                return self.claude_shared(u, method)
            if path == "/gateway/me/claude":
                return self.claude_own(u, method)
            if path.startswith("/claude/"):
                return self.claude(u, method, path[len("/claude"):])

            parts = path.split("/", 2)  # ['', 'ollama', 'api/chat']
            service = parts[1] if len(parts) > 1 else ""
            rest = "/" + (parts[2] if len(parts) > 2 else "")
            upstream = load(CONFIG, {}).get("upstreams", {}).get(service)
            if service not in SERVICE_PERM or not upstream:
                return self.error(404, "الخدمة هذي مو مضافة في البوابة.")
            if not has(u, SERVICE_PERM[service]):
                return self.error(403, "ما عندك صلاحية لهذي الخدمة.")
            if service == "ollama":
                return self.ollama(u, method, rest)
            return self.proxy(method, upstream, rest, self.body() if method in ("POST", "PATCH") else None)
        except (BrokenPipeError, ConnectionResetError):
            pass  # الجوال قفل الاتصال (مثل زر الإيقاف)
        except Exception as e:  # نرجّع خطأ واضح بدل ما ينقطع الاتصال
            try:
                self.error(500, "خطأ في البوابة: %s" % e)
            except Exception:
                pass

    # ── Ollama مع التحقق من الصلاحيات ──
    def ollama(self, u, method, rest):
        upstream = load(CONFIG, {})["upstreams"]["ollama"]
        owner = u["role"] == "owner"
        if not owner and rest not in OLLAMA_MEMBER_PATHS:
            return self.error(403, "هذي العملية للمالك بس.")

        data = self.body() if method in ("POST", "DELETE") else None
        if rest in ("/api/chat", "/api/generate") and data:
            req = json.loads(data or b"{}")
            model = req.get("model", "")
            if not model_allowed(u, model):
                return self.error(403, "الموديل %s مو مسموح لك." % model)
            msgs = req.get("messages", [])
            with_images = bool(req.get("images")) or any(m.get("images") for m in msgs)
            if with_images and not has(u, "images"):
                return self.error(403, "إرسال الصور مو مسموح لك.")

        if rest == "/api/tags" and method == "GET" and not owner:
            # نعرض له الموديلات المسموحة بس
            status, body = self.fetch(upstream, rest)
            if status == 200:
                tags = json.loads(body)
                tags["models"] = [m for m in tags.get("models", []) if model_allowed(u, m.get("name", ""))]
                return self.reply(200, tags)
            return self.error(status, "Ollama رد بخطأ.")

        if rest == "/api/pull" and method == "POST" and data:
            return self.pull_stream(upstream, data)
        if rest == "/api/chat" and method == "POST" and data and json.loads(data).get("stream", True) is not False:
            return self.chat_job(u, upstream, data)
        if rest in ("/api/chat", "/api/generate"):
            # نعدّ المحادثات الشغالة: التعلّم ينتظر لين Ollama يفضى
            with BUSY_LOCK:
                BUSY["active"] += 1
            try:
                return self.proxy(method, upstream, rest, data)
            finally:
                with BUSY_LOCK:
                    BUSY["active"] -= 1
                    BUSY["last"] = time.time()
        return self.proxy(method, upstream, rest, data)

    # ── وضع «دراسات»: أبحاث حقيقية من OpenAlex و PubMed ──
    def studies_api(self, u):
        if not has(u, "chat"):
            return self.error(403, "ما عندك صلاحية.")
        q = (urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query).get("q") or [""])[0].strip()[:300]
        if not q:
            return self.error(400, "السؤال فاضي.")
        try:
            n = max(3, min(int((urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query).get("n") or ["8"])[0]), 15))
        except ValueError:
            n = 8
        return self.reply(200, {"query": q, "studies": find_studies(q, n)})

    # ── نص أي ملف (Word / Excel / PowerPoint / EPUB / HTML …) للتطبيق ──
    def extract_api(self, u):
        if not has(u, "chat"):
            return self.error(403, "ما عندك صلاحية.")
        n = int(self.headers.get("Content-Length") or 0)
        if n > 25_000_000:
            return self.error(413, "الملف كبير (أكثر من 25MB).")
        name = urllib.parse.unquote(self.headers.get("X-Filename", "file"))[:200]
        try:
            text, pages = extract_text(name, self.body())
        except Exception as e:
            return self.error(422, "ما قدرت أقرأ الملف: %s" % e)
        if not text.strip():
            return self.error(422, "الملف ما فيه نص أقدر أقراه.")
        return self.reply(200, {"name": name, "text": text[:300_000], "pages": pages})

    # ── تنزيل موديل: يكمّل على الماك حتى لو الجوال انقطع، ولو رجعت تشوف نفس التقدّم ──
    def pull_stream(self, upstream, data):
        model = str(json.loads(data or b"{}").get("model") or json.loads(data or b"{}").get("name") or "").strip()
        if not model:
            return self.error(400, "اسم الموديل فاضي.")
        p = start_pull(upstream, model)
        self.send_response(200)
        self.send_header("Content-Type", "application/x-ndjson")
        self.send_header("Transfer-Encoding", "chunked")
        self.end_headers()
        i = 0
        try:
            while True:
                with p["cond"]:
                    p["cond"].wait_for(lambda: len(p["lines"]) > i or p["done"], timeout=20)
                    new = p["lines"][i:]
                    i += len(new)
                    finished = p["done"] and i >= len(p["lines"])
                    # الخط القديم ما يهم: نرسل آخر سطر بس (يكفي للتقدّم)
                    if len(new) > 1:
                        new = new[-1:]
                for line in new:
                    self.wfile.write(b"%x\r\n%s\r\n" % (len(line), line))
                self.wfile.flush()
                if finished:
                    break
            self.wfile.write(b"0\r\n\r\n")
            self.wfile.flush()
        except OSError:
            pass   # الجوال راح: التنزيل مكمّل بالخلفية

    # ── الرد يشتغل على الماك حتى لو الجوال انقطع (يطلع من التطبيق، تتغيّر الشبكة…) ──
    def chat_job(self, u, upstream, data):
        title = urllib.parse.unquote(self.headers.get("X-Chat-Title", ""))[:80]
        job = Job(u["id"], title, self.headers.get("X-Conversation", "")[:64])
        job.temporary = self.headers.get("X-Temporary") == "1"
        with JOBS_LOCK:
            for jid in [k for k, j in JOBS.items()
                        if time.time() - j.created > (JOB_TTL_TEMP if j.temporary else JOB_TTL)]:
                JOBS.pop(jid, None)
            JOBS[job.id] = job
        threading.Thread(target=job.run, args=(upstream, data), daemon=True).start()
        with job.cond:
            job.cond.wait_for(lambda: job.status is not None or job.done, timeout=600)
        self.send_response(job.status or 502)
        self.send_header("Content-Type", "application/x-ndjson")
        self.send_header("X-Job-Id", job.id)
        self.send_header("Transfer-Encoding", "chunked")
        self.end_headers()
        i = 0
        try:
            while True:
                with job.cond:
                    job.cond.wait_for(lambda: len(job.lines) > i or job.done, timeout=30)
                    new = job.lines[i:]
                    i += len(new)
                    finished = job.done and i >= len(job.lines)
                for line in new:
                    self.wfile.write(b"%x\r\n%s\r\n" % (len(line), line))
                self.wfile.flush()
                if finished:
                    break
            self.wfile.write(b"0\r\n\r\n")
            self.wfile.flush()
            if job.temporary:
                job.forget()   # محادثة مؤقتة: وصل الرد كامل، فما نخلي منه نسخة
        except OSError:
            if self.headers.get("X-Keep-Running") != "1":
                job.cancel()      # تطبيق قديم: الانقطاع معناه «أوقف» زي قبل
                return
            job.detached = True   # الجوال راح: الرد يكمّل، ولما يخلص ينرسل تنبيه
            if job.done:
                job.after_done()

    def job_api(self, u, method, path):
        parts = path[len("/gateway/jobs/"):].split("/")
        with JOBS_LOCK:
            job = JOBS.get(parts[0])
        if not job or job.user != u["id"]:
            return self.error(404, "الرد هذا مو موجود (يمكن البوابة أعادت التشغيل).")
        if method == "DELETE":
            job.cancel()
            return self.reply(200, {"cancelled": True})
        if method == "GET" and len(parts) == 1 and job.temporary and job.done:
            state = job.state()
            job.forget()
            return self.reply(200, state)
        if len(parts) > 1 and parts[1] == "notify" and method == "POST":
            # التطبيق راح للخلفية: أول ما يخلص الرد ارسل تنبيه
            job.notify = True
            if job.done:
                job.after_done()
            return self.reply(200, {"done": job.done})
        return self.reply(200, job.state())

    # ── ملخص الصباح ──
    def brief_api(self, u, method):
        if not has(u, "servers"):
            return self.error(403, "ما عندك صلاحية السيرفرات.")
        if method == "POST":
            if u["role"] != "owner":
                return self.error(403, "للمالك بس.")
            req = json.loads(self.body() or b"{}")
            with LOCK:
                cfg = load(CONFIG, {})
                b = cfg.setdefault("brief", {"enabled": True, "time": "07:00"})
                if "enabled" in req:
                    b["enabled"] = bool(req["enabled"])
                if re.fullmatch(r"\d{1,2}:\d{2}", str(req.get("time", ""))):
                    h, m = map(int, req["time"].split(":"))
                    b["time"] = "%02d:%02d" % (h % 24, m % 60)
                save(CONFIG, cfg)
        if "now" in urllib.parse.urlsplit(self.path).query:
            return self.reply(200, dict(build_brief(), settings=brief_settings()))
        latest = load(BRIEF, {})
        return self.reply(200, dict(latest, settings=brief_settings()))

    def set_name(self, u):
        name = str(json.loads(self.body() or b"{}").get("name", "")).strip()[:30]
        with LOCK:
            data = load(USERS, {"users": []})
            for x in data["users"]:
                if x["id"] == u["id"]:
                    if name:
                        x["display_name"] = name
                    else:
                        x.pop("display_name", None)
            save(USERS, data)
        return self.reply(200, {"name": name})

    def register_push(self, u):
        req = json.loads(self.body() or b"{}")
        token = re.sub(r"[^0-9a-fA-F]", "", str(req.get("token", "")))
        env = "sandbox" if req.get("env") == "sandbox" else "production"
        if not 32 <= len(token) <= 200:
            return self.error(400, "رمز التنبيهات غلط.")
        with LOCK:
            data = load(USERS, {"users": []})
            for x in data["users"]:
                if x["id"] == u["id"]:
                    tokens = [t for t in x.get("push", []) if t["token"] != token]
                    x["push"] = (tokens + [{"token": token, "env": env}])[-5:]
            save(USERS, data)
        return self.reply(200, {"push": bool(load(CONFIG, {}).get("apns"))})

    # ── تمرير الطلب (مع البث كلمة كلمة) ──
    def fetch(self, upstream, rest):
        target = urllib.parse.urlsplit(upstream)
        conn = http.client.HTTPConnection(target.hostname, target.port or 80, timeout=15)
        conn.request("GET", target.path.rstrip("/") + rest)
        r = conn.getresponse()
        return r.status, r.read()

    def proxy(self, method, upstream, rest, data, extra_headers=None, on_status=None):
        target = urllib.parse.urlsplit(upstream)
        query = urllib.parse.urlsplit(self.path).query
        path = target.path.rstrip("/") + rest + ("?" + query if query else "")
        if target.scheme == "https":
            conn = http.client.HTTPSConnection(target.hostname, target.port or 443, timeout=600)
        else:
            conn = http.client.HTTPConnection(target.hostname, target.port or 80, timeout=600)
        headers = {"Content-Type": self.headers.get("Content-Type", "application/json"), "Accept": "*/*"}
        headers.update(extra_headers or {})
        try:
            conn.request(method, path, body=data, headers=headers)
            r = conn.getresponse()
        except OSError:
            return self.error(502, "البوابة ما قدرت توصل للخدمة (%s). تأكد إنها شغالة." % target.netloc)
        if on_status:
            on_status(r.status)

        self.send_response(r.status)
        self.send_header("Content-Type", r.getheader("Content-Type", "application/json"))
        if method == "HEAD":
            self.send_header("Content-Length", "0")
            self.end_headers()
            conn.close()
            return
        self.send_header("Transfer-Encoding", "chunked")
        self.end_headers()
        while True:
            chunk = r.read1(65536) if hasattr(r, "read1") else r.read(4096)
            if not chunk:
                break
            self.wfile.write(b"%x\r\n%s\r\n" % (len(chunk), chunk))
            self.wfile.flush()
        self.wfile.write(b"0\r\n\r\n")
        self.wfile.flush()
        conn.close()

    # ── API البوابة ──
    def pair(self):
        req = json.loads(self.body() or b"{}")
        raw = str(req.get("code", ""))
        # أرقام عربية (٠١٢) أو مسافات: نحولها لأرقام إنجليزية
        code = "".join(str(int(ch)) for ch in raw if ch.isdigit())
        result, err = redeem(code, str(req.get("device", ""))[:40], self.client_address[0],
                             str(req.get("device_id", ""))[:64])
        if err:
            sys.stderr.write("pair failed: raw=%r\n" % raw)
            return self.error(403, err)
        user = next(x for x in load(USERS, {"users": []})["users"] if x["id"] == result["user"]["id"])
        result["services"] = services(user)
        self.reply(200, result)

    # ── التحديث بضغطة: ننزّل النسخة الجديدة، نتأكد إنها سليمة، ونعيد التشغيل ──
    def update(self, u, method):
        if u["role"] != "owner":
            return self.error(403, "للمالك بس.")
        url = load(CONFIG, {}).get("update_url", DEFAULT_UPDATE_URL)
        try:
            with urllib.request.urlopen(url, timeout=20) as r:
                code = r.read()
        except Exception:
            # بايثون الماك أحياناً ما يلقى شهادات SSL: نجرب curl
            try:
                code = subprocess.run(["curl", "-fsSL", "--max-time", "30", url], capture_output=True, check=True).stdout
            except Exception as e:
                return self.error(502, "ما قدرت أنزّل التحديث: %s" % e)
        m = re.search(rb'^VERSION = "([0-9.]+)"', code, re.M)
        if not m or b"class Gateway" not in code:
            return self.error(502, "الملف اللي نزل مو بوابة مساعدي.")
        latest = m.group(1).decode()
        newer = tuple(map(int, latest.split("."))) > tuple(map(int, VERSION.split(".")))
        if method == "GET" or not newer:
            return self.reply(200, {"version": VERSION, "latest": latest, "available": newer})
        try:
            compile(code, "gateway.py", "exec")
        except SyntaxError as e:
            return self.error(502, "التحديث فيه خطأ، ما ركّبته: %s" % e)
        me = os.path.abspath(__file__)
        shutil.copy2(me, me + ".bak")
        tmp = me + ".new"
        with open(tmp, "wb") as f:
            f.write(code)
        os.replace(tmp, me)
        self.reply(200, {"version": VERSION, "latest": latest, "updated": True})
        # launchd (KeepAlive) يشغّلها من جديد بالنسخة الجديدة
        threading.Timer(1.0, lambda: os._exit(0)).start()

    def me(self, u):
        self.reply(200, {"user": public(u), "services": services(u), "settings": shared_settings(u), "memory": u.get("memory", ""), "learned": u.get("learned"), "claude": {
            "shared": bool(shared_claude_key()), "own_key": bool(u.get("claude_key")),
            "limit": None if u["role"] == "owner" or u.get("claude_key") else u.get("claude_limit", CLAUDE_DEFAULT_LIMIT),
            "used": claude_used(u),
        }})

    # ── إعدادات مشتركة: الجهاز الجديد ياخذها تلقائياً بعد الربط ──
    def settings(self, u, method):
        if method == "POST":
            if u["role"] != "owner":
                return self.error(403, "للمالك بس.")
            req = json.loads(self.body() or b"{}")
            with LOCK:
                cfg = load(CONFIG, {})
                shared = cfg.setdefault("shared", {})
                for k in ("kuma_slug", "wake_url"):
                    if k in req:
                        v = str(req[k] or "").strip()
                        if v:
                            shared[k] = v
                        else:
                            shared.pop(k, None)
                save(CONFIG, cfg)
        return self.reply(200, shared_settings(u))

    # ── ذاكرتك: معلومات عنك تنضاف لكل محادثة، ومشتركة بين أجهزتك ──
    def memory(self, u, method):
        if method == "POST":
            text = str(json.loads(self.body() or b"{}").get("memory", ""))[:MAX_MEMORY]
            with LOCK:
                data = load(USERS, {"users": []})
                for x in data["users"]:
                    if x["id"] == u["id"]:
                        x["memory"] = text
                save(USERS, data)
            return self.reply(200, {"memory": text})
        return self.reply(200, {"memory": u.get("memory", "")})

    # ── يتعلّم من المحادثة: الموديل المحلي يطلّع معلومات ثابتة عنك (على الماك بس) ──
    def learn(self, u):
        """ما يشغّل الموديل الحين: يحطها في طابور، وتنعمل لما Ollama يفضى (ما تبطّئ أسئلتك)."""
        req = json.loads(self.body() or b"{}")
        model = str(req.get("model") or "")
        if not model or model.startswith("claude"):
            return self.error(400, "يحتاج موديل محلي.")
        lines = []
        for m in (req.get("messages") or [])[-24:]:
            text = str(m.get("content") or "").strip()[:2500]
            if text:
                lines.append(("المستخدم: " if m.get("role") == "user" else "المساعد: ") + text)
        if any(l.startswith("المستخدم") for l in lines):
            with BUSY_LOCK:
                # محادثة وحدة لكل شخص بالطابور (الأحدث تكفي)
                LEARN_QUEUE[:] = [j for j in LEARN_QUEUE if j["user"] != u["id"]]
                LEARN_QUEUE.append({"user": u["id"], "model": model, "convo": "\n\n".join(lines)[-14000:]})
            LEARN_EVENT.set()
        return self.reply(200, {"queued": True})

    # ── نسخة احتياطية للمحادثات: كل شخص له ملف واحد على الماك ──
    def backup(self, u, method):
        path = os.path.join(BACKUPS, re.sub(r"[^0-9a-f]", "", u["id"]) + ".json")
        if method == "POST":
            n = int(self.headers.get("Content-Length") or 0)
            if n <= 0 or n > MAX_BACKUP:
                return self.error(413, "النسخة كبيرة زيادة.")
            data = self.rfile.read(n)
            try:
                new = json.loads(data)
            except ValueError:
                return self.error(400, "ملف غير صالح.")
            # المحذوفات ما تضيع: نجمعها مع اللي في النسخة القديمة (لو جهاز بتطبيق قديم رفع بدونها)
            try:
                old = json.load(open(path)) if os.path.exists(path) else {}
            except ValueError:
                old = {}
            for field in ("deleted", "deletedMessages"):
                merged = dict(old.get(field) or {})
                for k, v in (new.get(field) or {}).items():
                    merged[k] = max(int(v), int(merged.get(k, 0)))
                if merged:
                    new[field] = merged
            deleted = new.get("deleted") or {}
            if new.get("deleted") or new.get("deletedMessages"):
                new["conversations"] = [c for c in new.get("conversations", [])
                                        if str(min((m.get("createdAt", 0) for m in c.get("messages", [])), default=0)) not in deleted]
                data = json.dumps(new, ensure_ascii=False).encode()
            os.makedirs(BACKUPS, exist_ok=True)
            tmp = path + ".tmp"
            with open(tmp, "wb") as f:
                f.write(data)
            os.replace(tmp, path)
            return self.reply(200, {"size": n, "at": int(os.path.getmtime(path))})
        if method == "DELETE":
            if os.path.exists(path):
                os.remove(path)
            return self.reply(200, {"deleted": True})
        if not os.path.exists(path):
            return self.error(404, "ما فيه نسخة محفوظة على الماك.")
        if "info" in urllib.parse.urlsplit(self.path).query:
            return self.reply(200, {"size": os.path.getsize(path), "at": int(os.path.getmtime(path))})
        with open(path, "rb") as f:
            data = f.read()
        self.send_response(200)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    # ── صور المحادثات: كل صورة ترتفع مرة وحدة (اسمها = بصمتها sha256) ──
    def image(self, u, method, digest):
        if not re.fullmatch(r"[0-9a-f]{64}", digest):
            return self.error(400, "اسم صورة غلط.")
        folder = os.path.join(IMAGES, re.sub(r"[^0-9a-f]", "", u["id"]))
        path = os.path.join(folder, digest)
        if method == "PUT":
            n = int(self.headers.get("Content-Length") or 0)
            if n <= 0 or n > MAX_IMAGE:
                return self.error(413, "الصورة كبيرة زيادة.")
            data = self.rfile.read(n)
            if hashlib.sha256(data).hexdigest() != digest:
                return self.error(400, "الصورة وصلت ناقصة.")
            os.makedirs(folder, exist_ok=True)
            with open(path + ".tmp", "wb") as f:
                f.write(data)
            os.replace(path + ".tmp", path)
            return self.reply(200, {"ok": True})
        if not os.path.exists(path):
            return self.error(404, "الصورة مو موجودة.")
        if method == "HEAD":
            self.send_response(200)
            self.send_header("Content-Length", "0")
            self.end_headers()
            return
        with open(path, "rb") as f:
            data = f.read()
        self.send_response(200)
        self.send_header("Content-Type", "application/octet-stream")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    # ── Claude: مفتاح المالك مع حد يومي، أو مفتاح الشخص نفسه بدون حد ──
    def claude_shared(self, u, method):
        if u["role"] != "owner":
            return self.error(403, "للمالك بس.")
        if method == "POST":
            key = str(json.loads(self.body() or b"{}").get("key", "")).strip()
            with LOCK:
                cfg = load(CONFIG, {})
                if key:
                    cfg["claude_key"] = key
                else:
                    cfg.pop("claude_key", None)
                save(CONFIG, cfg)
        return self.reply(200, {"shared": bool(shared_claude_key())})

    def claude_own(self, u, method):
        if not has(u, "claude"):
            return self.error(403, "Claude مو مسموح لك.")
        if method == "POST":
            key = str(json.loads(self.body() or b"{}").get("key", "")).strip()
            with LOCK:
                data = load(USERS, {"users": []})
                for x in data["users"]:
                    if x["id"] == u["id"]:
                        if key:
                            x["claude_key"] = key
                        else:
                            x.pop("claude_key", None)
                save(USERS, data)
        return self.me(find_user_by_id(u["id"]))

    def claude(self, u, method, rest):
        if not has(u, "claude"):
            return self.error(403, "Claude مو مسموح لك.")
        if (method, rest) not in (("POST", "/v1/messages"), ("GET", "/v1/models")):
            return self.error(403, "هذي العملية مو مسموحة.")
        own = u.get("claude_key")
        key = own or shared_claude_key()
        if not key:
            return self.error(503, "Claude مو مفعّل في البوابة. المالك يضيف مفتاحه من الإعدادات ← العائلة.")
        limited = not own and u["role"] != "owner"
        limit = u.get("claude_limit", CLAUDE_DEFAULT_LIMIT)
        counting = method == "POST"
        if counting and limited and claude_used(u) >= limit:
            return self.error(429, "خلصت رسائل Claude اليوم (%d). ترجع بكرة، أو حط مفتاحك الخاص من الإعدادات." % limit)

        data = self.body() if method == "POST" else None
        if data and not has(u, "images") and b'"type":"image"' in data.replace(b" ", b""):
            return self.error(403, "إرسال الصور مو مسموح لك.")

        def counted(status):
            if counting and status == 200:
                with LOCK:
                    users = load(USERS, {"users": []})
                    for x in users["users"]:
                        if x["id"] == u["id"]:
                            x["claude_usage"] = {"day": today(), "count": claude_used(x) + 1}
                    save(USERS, users)

        headers = {"x-api-key": key, "anthropic-version": self.headers.get("anthropic-version", "2023-06-01")}
        return self.proxy(method, load(CONFIG, {}).get("claude_api", CLAUDE_API), rest, data, headers, counted)

    def users(self, u, method, path):
        if u["role"] != "owner":
            return self.error(403, "إدارة العائلة للمالك بس.")
        user_id = path[len("/gateway/users"):].strip("/")
        with LOCK:
            data = load(USERS, {"users": []})
            if method == "GET" and not user_id:
                return self.reply(200, {"users": [public(x) for x in data["users"]]})

            if method == "POST" and not user_id:
                req = json.loads(self.body() or b"{}")
                user = {
                    "id": secrets.token_hex(4), "name": req.get("name", "شخص")[:40], "role": "member",
                    "token_hash": token_hash(new_token()),  # يتغيّر لما يمسح رمز الدعوة
                    "perms": {p: bool(req.get("perms", {}).get(p)) for p in PERMS},
                    "models": req.get("models", ["*"]), "disabled": False, "created": now(), "last_used": 0,
                    "paired": False, "claude_limit": int(req.get("claude_limit", CLAUDE_DEFAULT_LIMIT)),
                }
                data["users"].append(user)
                save(USERS, data)
                code = create_pair_code("member", user["id"])
                user["invite_expires"] = now() + 600
                return self.reply(200, {"user": public(user), "code": code, "expires_in": 600})

            user = next((x for x in data["users"] if x["id"] == user_id), None)
            if not user:
                return self.error(404, "ما لقيت هذا الشخص.")

            if method == "PATCH":
                req = json.loads(self.body() or b"{}")
                for key in ("name", "models", "disabled"):
                    if key in req and user["role"] != "owner":
                        user[key] = req[key]
                if "claude_limit" in req:
                    user["claude_limit"] = max(0, min(500, int(req["claude_limit"])))
                if "perms" in req and user["role"] != "owner":
                    user["perms"] = {p: bool(req["perms"].get(p)) for p in PERMS}
                save(USERS, data)
                return self.reply(200, {"user": public(user)})

            if method == "POST" and path.endswith("/code"):
                return self.reply(200, {"code": create_pair_code(user["role"], user["id"]), "expires_in": 600})

            if method == "DELETE":
                if user["role"] == "owner" and sum(1 for x in data["users"] if x["role"] == "owner") == 1:
                    return self.error(400, "ما تقدر تحذف آخر مالك.")
                data["users"] = [x for x in data["users"] if x["id"] != user_id]
                save(USERS, data)
                return self.reply(200, {"ok": True})
        self.error(405, "طلب غير مدعوم.")


# ─────────── قفل Ollama ───────────

ENV_PLIST = os.path.expanduser("~/Library/LaunchAgents/com.user.ollama-env.plist")


def ollama_locked():
    """مقفول = Ollama يسمع على الماك نفسه بس (127.0.0.1)."""
    try:
        out = subprocess.run(["launchctl", "getenv", "OLLAMA_HOST"], capture_output=True, text=True, timeout=5).stdout
        return out.strip().startswith("127.0.0.1")
    except Exception:
        return False


def set_ollama_lock(locked):
    """يغيّر OLLAMA_HOST ويعيد تشغيل Ollama. يرجّع رسالة خطأ أو None."""
    to = "127.0.0.1:11434" if locked else "0.0.0.0:11434"
    frm = "0.0.0.0:11434" if locked else "127.0.0.1:11434"
    try:
        # نثبّت الإعداد بعد إعادة تشغيل الماك
        if os.path.exists(ENV_PLIST):
            with open(ENV_PLIST, encoding="utf-8") as f:
                text = f.read()
            with open(ENV_PLIST, "w", encoding="utf-8") as f:
                f.write(text.replace("OLLAMA_HOST " + frm, "OLLAMA_HOST " + to))
        subprocess.run(["launchctl", "setenv", "OLLAMA_HOST", to], check=True, timeout=5)
        subprocess.run(["osascript", "-e", 'quit app "Ollama"'], timeout=10)
        time.sleep(2)
        subprocess.run(["open", "-a", "Ollama"], timeout=10)
    except Exception as e:
        return "ما قدرت أغيّر إعداد Ollama: %s" % e
    # ننتظر Ollama يرجع (لين 20 ثانية)
    for _ in range(20):
        time.sleep(1)
        try:
            conn = http.client.HTTPConnection("127.0.0.1", 11434, timeout=2)
            conn.request("GET", "/")
            if conn.getresponse().status == 200:
                return None
        except OSError:
            pass
    return "Ollama ما رجع يشتغل. افتحه يدوي على الماك."


CLAUDE_API = "https://api.anthropic.com"


def shared_claude_key():
    return load(CONFIG, {}).get("claude_key", "")


LEARN_PROMPT = """مهمتك تطلّع من المحادثة معلومات ثابتة عن المستخدم نفسه، تفيد مساعده في محادثات جاية.

احفظ بس:
- اسمه، شغله، مدينته، لغته أو لهجته
- أجهزته وأنظمته وسيرفراته ومشاريعه المستمرة
- طريقته المفضّلة في الردود (مختصر، بالعامية، بالتفصيل…)
- اهتمامات ثابتة ذكرها هو بنفسه

لا تحفظ:
- أشياء مؤقتة (اليوم، بكرة، موعد، مزاج، مشكلة انحلّت)
- معلومات عن ناس ثانيين، أو أسئلة عامة ما تخصّه
- أي شي قاله المساعد وما أكّده المستخدم
- كلمات سر، مفاتيح، أرقام حسابات أو هويات
- صحة أو أمراض أو أمور حساسة

اللي محفوظ من قبل (لا تكرره):
{memory}

المحادثة:
{convo}

رد بـ JSON بس بهالشكل: {"facts": ["جملة قصيرة", ...]}
كل جملة بالعربي، قصيرة، بصيغة الغائب (مثل: يشتغل مطوّر تطبيقات). لو ما فيه شي جديد يستاهل: {"facts": []}"""


# ── الردود بالخلفية ──
JOBS = {}
JOBS_LOCK = threading.Lock()
JOB_TTL = 6 * 3600
JOB_TTL_TEMP = 15 * 60   # المؤقتة: لو ما رجع لها أحد، تنمسح بعد ربع ساعة


class Job:
    """رد واحد: يقرا من Ollama ويحفظ كل سطر، وأي اتصال (أو إعادة اتصال) يقرا منه."""

    def __init__(self, user, title, conversation):
        self.id = secrets.token_hex(8)
        self.user = user
        self.title = title
        self.conversation = conversation
        self.created = time.time()
        self.cond = threading.Condition()
        self.lines = []
        self.status = None
        self.done = False
        self.error = None
        self.content = []
        self.thinking = []
        self.final = {}
        self.notify = False
        self.detached = False
        self.cancelled = False
        self.pushed = False
        self.temporary = False   # محادثة مؤقتة: ما نخلي منها نسخة بعد ما توصل
        self.conn = None

    def run(self, upstream, data):
        with BUSY_LOCK:
            BUSY["active"] += 1
        try:
            target = urllib.parse.urlsplit(upstream)
            self.conn = http.client.HTTPConnection(target.hostname, target.port or 80, timeout=600)
            self.conn.request("POST", target.path.rstrip("/") + "/api/chat", body=data,
                              headers={"Content-Type": "application/json"})
            r = self.conn.getresponse()
            with self.cond:
                self.status = r.status
                self.cond.notify_all()
            buf = b""
            while not self.cancelled:
                chunk = r.read1(65536)
                if not chunk:
                    break
                buf += chunk
                while b"\n" in buf:
                    line, buf = buf.split(b"\n", 1)
                    if line.strip():
                        self.add(line + b"\n")
            if buf.strip():
                self.add(buf.strip() + b"\n")
        except Exception as e:
            if not self.cancelled:
                self.error = "البوابة ما قدرت تكمّل مع Ollama: %s" % e
                with self.cond:
                    if self.status is None:
                        self.status = 502
                self.add(json.dumps({"error": self.error}, ensure_ascii=False).encode() + b"\n")
        finally:
            with BUSY_LOCK:
                BUSY["active"] -= 1
                BUSY["last"] = time.time()
            try:
                self.conn and self.conn.close()
            except Exception:
                pass
            with self.cond:
                self.done = True
                self.cond.notify_all()
            self.after_done()

    def add(self, line):
        try:
            d = json.loads(line)
        except ValueError:
            d = {}
        msg = d.get("message") or {}
        with self.cond:
            if msg.get("content"):
                self.content.append(msg["content"])
            if msg.get("thinking"):
                self.thinking.append(msg["thinking"])
            if d.get("error"):
                self.error = d["error"]
            if d.get("done"):
                self.final = {k: d.get(k) for k in ("done_reason", "eval_count", "eval_duration", "total_duration")}
            self.lines.append(line)
            self.cond.notify_all()

    def cancel(self):
        self.cancelled = True
        try:
            self.conn and self.conn.sock and self.conn.sock.shutdown(2)   # Ollama يوقف الكتابة
        except Exception:
            pass

    def state(self):
        with self.cond:
            return dict(self.final, id=self.id, done=self.done, error=self.error,
                        content="".join(self.content), thinking="".join(self.thinking))

    def forget(self):
        """يمسح محتوى الرد من البوابة (للمحادثة المؤقتة)."""
        with self.cond:
            self.lines, self.content, self.thinking = [], [], []
        with JOBS_LOCK:
            JOBS.pop(self.id, None)

    def after_done(self):
        """لو أحد طلب تنبيه (أو الجوال انقطع): نرسله مرة وحدة."""
        if self.pushed or self.cancelled or not (self.notify or self.detached):
            return
        self.pushed = True
        text = re.sub(r"[#*`>_\[\]]", "", "".join(self.content)).strip()
        if self.temporary:
            # المحادثة المؤقتة: التنبيه ما يبين شي من الرد (ولا العنوان)
            self.title = "مساعدي"
            body = "الرد جاهز في المحادثة المؤقتة"
        elif self.error and not text:
            body = "ما اكتمل الرد. افتح المحادثة وجرّب مرة ثانية."
        else:
            body = re.sub(r"\s+", " ", text)[:180] or "الرد جاهز"
        threading.Thread(target=send_push, args=(self.user, self.title or "الرد جاهز", body,
                                                  {"conversation": self.conversation, "job": self.id}),
                         daemon=True).start()


# ── البحث في الدراسات (بدون مفاتيح: OpenAlex + PubMed) ──
STUDIES_UA = "Mosaadi/1.0 (private self-hosted assistant)"


def _get_json(url, timeout=15):
    r = urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": STUDIES_UA}), timeout=timeout)
    return json.loads(r.read().decode("utf-8", "replace"))


def _openalex(q, n):
    url = "https://api.openalex.org/works?" + urllib.parse.urlencode({
        "search": q, "per-page": n, "filter": "has_abstract:true,type:article|review",
        "select": "title,publication_year,primary_location,abstract_inverted_index,doi,id,cited_by_count,type,authorships",
    })
    out = []
    for w in _get_json(url).get("results", []):
        inv = w.get("abstract_inverted_index") or {}
        words = sorted((pos, word) for word, positions in inv.items() for pos in positions)
        abstract = " ".join(word for _, word in words)
        loc = (w.get("primary_location") or {})
        venue = ((loc.get("source") or {}).get("display_name")) or ""
        authors = [((a.get("author") or {}).get("display_name") or "") for a in (w.get("authorships") or [])[:3]]
        out.append({
            "title": (w.get("title") or "").strip(), "year": w.get("publication_year"), "venue": venue,
            "authors": [a for a in authors if a], "abstract": abstract[:2500],
            "url": w.get("doi") or loc.get("landing_page_url") or w.get("id") or "",
            "source": "OpenAlex", "cited": w.get("cited_by_count") or 0,
            "review": w.get("type") == "review",
        })
    return out


def _pubmed(q, n):
    base = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/"
    ids = _get_json(base + "esearch.fcgi?" + urllib.parse.urlencode(
        {"db": "pubmed", "term": q, "retmax": n, "retmode": "json", "sort": "relevance"})).get("esearchresult", {}).get("idlist", [])
    if not ids:
        return []
    xml = urllib.request.urlopen(urllib.request.Request(base + "efetch.fcgi?" + urllib.parse.urlencode(
        {"db": "pubmed", "id": ",".join(ids), "retmode": "xml"}), headers={"User-Agent": STUDIES_UA}), timeout=15).read().decode("utf-8", "replace")
    out = []
    for art in re.findall(r"(?s)<PubmedArticle>(.*?)</PubmedArticle>", xml):
        pmid = (re.search(r"<PMID[^>]*>(\d+)</PMID>", art) or [None, ""])[1]
        title = _xml_text((re.search(r"(?s)<ArticleTitle>(.*?)</ArticleTitle>", art) or [None, ""])[1])
        abstract = " ".join(_xml_text(a) for a in re.findall(r"(?s)<AbstractText[^>]*>(.*?)</AbstractText>", art))
        year = (re.search(r"(?s)<PubDate>.*?<Year>(\d{4})</Year>", art) or [None, None])[1]
        venue = _xml_text((re.search(r"(?s)<Journal>.*?<Title>(.*?)</Title>", art) or [None, ""])[1])
        types = re.findall(r"<PublicationType[^>]*>(.*?)</PublicationType>", art)
        if not abstract:
            continue
        out.append({
            "title": title, "year": int(year) if year else None, "venue": venue, "authors": [],
            "abstract": abstract[:2500], "url": "https://pubmed.ncbi.nlm.nih.gov/%s/" % pmid, "source": "PubMed", "cited": 0,
            "review": any(t in ("Meta-Analysis", "Systematic Review", "Review") for t in types),
        })
    return out


def find_studies(q, n=8):
    results, errors = [], []

    def run(fn, k):
        try:
            results.extend(fn(q, k))
        except Exception as e:
            errors.append("%s: %s" % (fn.__name__, e))

    threads = [threading.Thread(target=run, args=(_openalex, n)), threading.Thread(target=run, args=(_pubmed, max(3, n // 2)))]
    for t in threads:
        t.start()
    for t in threads:
        t.join(25)
    seen, out = set(), []
    # المراجعات المنهجية أول، بعدين الأكثر استشهاد
    for r in sorted(results, key=lambda r: (not r["review"], -(r["cited"] or 0))):
        key = re.sub(r"\W+", "", (r["title"] or "").lower())[:80]
        if not key or key in seen:
            continue
        seen.add(key)
        out.append(r)
    if errors:
        print("studies: " + "; ".join(errors), flush=True)
    return out[:n]


# ── استخراج النص من الملفات (مكتبة Python العادية بس) ──
def _xml_text(xml, para_tags=("w:p", "a:p", "text:p", "text:h", "p", "div", "br", "li", "tr", "h1", "h2", "h3")):
    xml = re.sub(r"(?is)<(script|style)[^>]*>.*?</\1>", " ", xml)
    for t in para_tags:
        xml = re.sub(r"(?i)</%s>|<%s\s*/>" % (re.escape(t), re.escape(t)), "\n", xml)
    xml = re.sub(r"(?i)<w:tab\s*/>|<text:tab\s*/>", "\t", xml)
    xml = re.sub(r"(?i)<w:br\s*/>|<a:br\s*/>|<text:line-break\s*/>", "\n", xml)
    txt = htmllib.unescape(re.sub(r"<[^>]+>", "", xml))
    txt = re.sub(r"[ \t\u00a0]+", " ", txt)
    return re.sub(r"\n\s*\n\s*\n+", "\n\n", txt).strip()


def _num(name):
    m = re.search(r"(\d+)", name)
    return int(m.group(1)) if m else 0


def extract_text(name, data):
    """يرجّع (النص، عدد الصفحات/الشرائح/الأوراق)."""
    ext = name.rsplit(".", 1)[-1].lower() if "." in name else ""
    if ext in ("docx", "docm", "dotx", "xlsx", "xlsm", "pptx", "pptm", "epub", "odt", "ods", "odp"):
        z = zipfile.ZipFile(io.BytesIO(data))
        names = z.namelist()
        read = lambda n: z.read(n).decode("utf-8", "replace")
        if ext.startswith("doc"):
            parts = ["word/document.xml"] + sorted(n for n in names if re.match(r"word/(footnotes|endnotes)\.xml", n))
            return "\n\n".join(_xml_text(read(n)) for n in parts if n in names), 1
        if ext.startswith("ppt"):
            slides = sorted((n for n in names if re.match(r"ppt/slides/slide\d+\.xml$", n)), key=_num)
            out = []
            for i, n in enumerate(slides, 1):
                notes = "ppt/notesSlides/notesSlide%d.xml" % _num(n)
                body = _xml_text(read(n))
                if notes in names:
                    nt = _xml_text(read(notes))
                    if nt:
                        body += "\n(ملاحظات: %s)" % nt
                out.append("── شريحة %d ──\n%s" % (i, body))
            return "\n\n".join(out), len(slides)
        if ext.startswith("xls"):
            shared = []
            if "xl/sharedStrings.xml" in names:
                for si in re.findall(r"(?s)<si>(.*?)</si>", read("xl/sharedStrings.xml")):
                    shared.append(htmllib.unescape("".join(re.findall(r"(?s)<t[^>]*>(.*?)</t>", si))))
            wb = read("xl/workbook.xml") if "xl/workbook.xml" in names else ""
            titles = re.findall(r'<sheet [^>]*name="([^"]+)"', wb)
            sheets = sorted((n for n in names if re.match(r"xl/worksheets/sheet\d+\.xml$", n)), key=_num)
            out, total = [], 0
            for i, n in enumerate(sheets):
                rows = []
                for row in re.findall(r"(?s)<row[^>]*>(.*?)</row>", read(n)):
                    cells = []
                    for attrs, inner in re.findall(r"(?s)<c([^>]*)>(.*?)</c>", row):
                        v = re.search(r"(?s)<v>(.*?)</v>", inner)
                        isv = re.search(r"(?s)<is>.*?<t[^>]*>(.*?)</t>", inner)
                        if 't="s"' in attrs and v:
                            try:
                                cells.append(shared[int(v.group(1))])
                            except (ValueError, IndexError):
                                cells.append("")
                        elif isv:
                            cells.append(htmllib.unescape(isv.group(1)))
                        else:
                            cells.append(htmllib.unescape(v.group(1)) if v else "")
                    if any(c.strip() for c in cells):
                        rows.append(" | ".join(c.replace("\n", " ") for c in cells))
                    total += 1
                    if total > 5000:
                        break
                title = titles[i] if i < len(titles) else "ورقة %d" % (i + 1)
                out.append("── %s ──\n%s" % (title, "\n".join(rows)))
            return "\n\n".join(out), len(sheets)
        if ext == "epub":
            opf = next((n for n in names if n.endswith(".opf")), None)
            order = []
            if opf:
                o = read(opf)
                base = opf.rsplit("/", 1)[0] + "/" if "/" in opf else ""
                items = dict(re.findall(r'<item [^>]*id="([^"]+)"[^>]*href="([^"]+)"', o))
                items.update({k: v for v, k in re.findall(r'<item [^>]*href="([^"]+)"[^>]*id="([^"]+)"', o)})
                order = [base + urllib.parse.unquote(items[i]) for i in re.findall(r'<itemref [^>]*idref="([^"]+)"', o) if i in items]
            order = [n for n in order if n in names] or sorted(n for n in names if n.endswith((".xhtml", ".html", ".htm")))
            return "\n\n".join(_xml_text(read(n)) for n in order), len(order)
        # OpenDocument
        return _xml_text(read("content.xml")), 1
    text = data.decode("utf-8", "replace")
    if ext == "rtf":
        text = re.sub(r"\\'([0-9a-f]{2})", lambda m: bytes.fromhex(m.group(1)).decode("cp1256", "replace"), text)
        text = re.sub(r"\\u(-?\d+)\??", lambda m: chr(int(m.group(1)) % 65536), text)
        text = re.sub(r"\\par[d]?\b", "\n", text)
        text = re.sub(r"\\[a-zA-Z]+-?\d* ?|[{}]", "", text)
        return text.strip(), 1
    if ext in ("html", "htm", "xhtml", "xml", "svg"):
        return _xml_text(text), 1
    # نص عادي؟ (مو ملف ثنائي)
    if data[:4000].count(b"\x00") == 0:
        return text, 1
    raise ValueError("هالنوع ما أعرف أقراه (%s)" % (ext or "بدون امتداد"))


# ── تنزيلات الموديلات بالخلفية ──
PULLS = {}
PULLS_LOCK = threading.Lock()


def start_pull(upstream, model):
    """يبدأ تنزيل (أو يرجّع اللي شغّال لنفس الموديل). Ollama يكمّل من حيث وقف لو انقطع قبل."""
    with PULLS_LOCK:
        p = PULLS.get(model)
        if p and (not p["done"] or time.time() - p["at"] < 5):
            return p
        p = {"lines": [], "done": False, "at": time.time(), "cond": threading.Condition()}
        PULLS[model] = p

    def run():
        def add(line):
            with p["cond"]:
                p["lines"].append(line)
                del p["lines"][:-50]
                p["cond"].notify_all()
        for attempt in range(5):     # النت قطع؟ نعيد (Ollama يكمّل من نفس النقطة)
            try:
                r = urllib.request.urlopen(urllib.request.Request(
                    upstream.rstrip("/") + "/api/pull", data=json.dumps({"model": model, "stream": True}).encode(),
                    headers={"Content-Type": "application/json"}), timeout=120)
                ok = False
                for raw in r:
                    raw = raw.strip()
                    if not raw:
                        continue
                    add(raw)
                    try:
                        st = json.loads(raw)
                    except ValueError:
                        continue
                    if st.get("error"):
                        attempt = 99
                        break
                    if st.get("status") == "success":
                        ok = True
                if ok or attempt == 99:
                    break
            except Exception as e:
                if attempt == 4:
                    add(json.dumps({"error": "التنزيل وقف: %s" % e}).encode())
                time.sleep(3)
        with p["cond"]:
            p["done"] = True
            p["at"] = time.time()
            p["cond"].notify_all()

    threading.Thread(target=run, daemon=True).start()
    return p


# ── تنبيهات الآيفون (Apple Push) ──
_APNS_JWT = [None, 0]


def _b64url(b):
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode()


def _der_to_raw(der):
    """توقيع openssl (DER) ← الصيغة اللي تبيها Apple (r||s، 64 بايت)."""
    i = 2 if der[1] < 0x80 else 2 + (der[1] & 0x7F)
    out = b""
    for _ in range(2):
        n = der[i + 1]
        v = der[i + 2:i + 2 + n].lstrip(b"\x00")
        out += v.rjust(32, b"\x00")
        i += 2 + n
    return out


def apns_jwt(apns):
    if _APNS_JWT[0] and time.time() - _APNS_JWT[1] < 2400:
        return _APNS_JWT[0]
    head = _b64url(json.dumps({"alg": "ES256", "kid": apns["key_id"]}).encode())
    claims = _b64url(json.dumps({"iss": apns["team_id"], "iat": int(time.time())}).encode())
    msg = (head + "." + claims).encode()
    der = subprocess.run(["openssl", "dgst", "-sha256", "-sign", os.path.join(HOME, "apns.p8")],
                         input=msg, capture_output=True, check=True).stdout
    token = msg.decode() + "." + _b64url(_der_to_raw(der))
    _APNS_JWT[:] = [token, time.time()]
    return token


def send_push(user_id, title, body, extra=None):
    """يرسل لكل أجواله (الآيفون). يرجع كم وصل."""
    apns = load(CONFIG, {}).get("apns")
    u = find_user_by_id(user_id)
    if not apns or not u or not u.get("push"):
        return 0
    payload = json.dumps(dict(extra or {}, aps={
        "alert": {"title": title, "body": body}, "sound": "default",
        "thread-id": (extra or {}).get("conversation") or "chat"}), ensure_ascii=False).encode()
    sent, dead = 0, []
    for t in u["push"]:
        host = "api.sandbox.push.apple.com" if t.get("env") == "sandbox" else "api.push.apple.com"
        try:
            r = subprocess.run(
                ["curl", "-sS", "--http2", "-m", "20", "-w", "\n%{http_code}",
                 "-H", "authorization: bearer " + apns_jwt(apns),
                 "-H", "apns-topic: " + apns.get("topic", "com.imosaab.mosaadi"),
                 "-H", "apns-push-type: alert", "-H", "apns-priority: 10",
                 "--data-binary", "@-", "https://%s/3/device/%s" % (host, t["token"])],
                input=payload, capture_output=True, timeout=30)
            out = r.stdout.decode(errors="replace").rsplit("\n", 1)
            code = out[-1].strip()
            if code == "200":
                sent += 1
            elif code == "410" or "BadDeviceToken" in out[0] or "Unregistered" in out[0]:
                dead.append(t["token"])
            else:
                sys.stderr.write("push failed %s: %s %s\n" % (code, out[0], r.stderr.decode(errors="replace")))
        except Exception as e:
            sys.stderr.write("push failed: %s\n" % e)
    if dead:
        with LOCK:
            data = load(USERS, {"users": []})
            for x in data["users"]:
                if x["id"] == user_id:
                    x["push"] = [t for t in x.get("push", []) if t["token"] not in dead]
            save(USERS, data)
    return sent


# ── ملخص الصباح: كل يوم يجمع حالة السيرفرات والأقراص، ويرسلها تنبيه ──
BRIEF = os.path.join(HOME, "brief.json")


def brief_settings():
    b = load(CONFIG, {}).get("brief") or {}
    return {"enabled": b.get("enabled", True), "time": b.get("time", "07:00")}


def _get_json(url, timeout=8):
    with urllib.request.urlopen(url, timeout=timeout) as r:
        return json.loads(r.read())


def build_brief():
    cfg = load(CONFIG, {})
    up = cfg.get("upstreams", {})
    lines, stats = [], {}

    # السيرفرات (Uptime Kuma)
    slug = (cfg.get("shared") or {}).get("kuma_slug")
    if up.get("kuma") and slug:
        try:
            base = up["kuma"].rstrip("/")
            page = _get_json("%s/api/status-page/%s" % (base, slug))
            names = {m["id"]: m["name"] for g in page.get("publicGroupList", []) for m in g.get("monitorList", [])}
            beats = _get_json("%s/api/status-page/heartbeat/%s" % (base, slug)).get("heartbeatList", {})
            since = time.time() - 12 * 3600
            down_now, night = [], []
            for mid, name in names.items():
                hb = beats.get(str(mid)) or []
                if hb and hb[-1].get("status") != 1:
                    down_now.append(name)
                bad = 0
                for h in hb:
                    try:
                        t = time.mktime(time.strptime(h["time"][:19], "%Y-%m-%d %H:%M:%S")) - time.timezone
                    except (KeyError, ValueError):
                        continue
                    if t >= since and h.get("status") == 0:
                        bad += 1
                if bad and name not in down_now:
                    night.append(name)
            stats["servers_up"] = len(names) - len(down_now)
            stats["servers_total"] = len(names)
            if down_now:
                lines.append("⚠️ واقف الحين: " + "، ".join(down_now))
            else:
                lines.append("✅ كل السيرفرات شغالة (%d)" % len(names))
            if night:
                lines.append("بالليل وقف شوي ورجع: " + "، ".join(night))
        except Exception as e:
            lines.append("ما قدرت أوصل لـ Uptime Kuma (%s)" % type(e).__name__)

    # الـ NAS
    if up.get("nas"):
        try:
            fs = _get_json(up["nas"].rstrip("/") + "/api/4/fs")
            vols = [f for f in fs if str(f.get("mnt_point", "")).startswith("/volume")] or fs
            big = max(vols, key=lambda f: f.get("size", 0))
            stats["nas_percent"] = round(big.get("percent", 0))
            lines.append("💾 الـ NAS: %d%% مستخدم" % stats["nas_percent"]
                         + (" — قرّب يمتلي!" if stats["nas_percent"] >= 85 else ""))
        except Exception:
            lines.append("ما قدرت أوصل للـ NAS")

    # الماك
    try:
        total, used, free = shutil.disk_usage("/")
        stats["mac_free_gb"] = round(free / 1024 ** 3)
        lines.append("🖥️ الماك: فاضي %d GB" % stats["mac_free_gb"])
    except OSError:
        pass

    text = "\n".join(lines) or "ما فيه شي أبلّغك عنه."
    return {"date": time.strftime("%Y-%m-%d"), "at": int(time.time()),
            "title": "صباح الخير ☀︎ ملخص اليوم", "text": text, "stats": stats}


def brief_worker():
    """يصحى كل نص دقيقة: لو جا الوقت وما انرسل اليوم، يجهّز الملخص ويرسله."""
    while True:
        time.sleep(30)
        try:
            b = brief_settings()
            if not b["enabled"] or time.strftime("%H:%M") < b["time"]:
                continue
            if load(BRIEF, {}).get("date") == time.strftime("%Y-%m-%d"):
                continue
            brief = build_brief()
            save(BRIEF, brief)
            short = re.sub(r"\s+", " ", brief["text"].replace("\n", " · "))[:180]
            for x in load(USERS, {"users": []})["users"]:
                if x.get("push") and has(x, "servers") and not x.get("disabled"):
                    send_push(x["id"], brief["title"], short, {"brief": True})
        except Exception as e:
            sys.stderr.write("brief failed: %s\n" % e)


# ── التعلّم بالخلفية ──
BUSY = {"active": 0, "last": 0.0}
BUSY_LOCK = threading.Lock()
LEARN_QUEUE = []
LEARN_EVENT = threading.Event()
LEARN_IDLE = 45   # ثواني بدون أسئلة قبل ما يبدأ


def learn_worker():
    while True:
        LEARN_EVENT.wait()
        while True:
            with BUSY_LOCK:
                idle = BUSY["active"] == 0 and time.time() - BUSY["last"] > LEARN_IDLE
                job = LEARN_QUEUE.pop(0) if idle and LEARN_QUEUE else None
                if not LEARN_QUEUE and job is None and idle:
                    LEARN_EVENT.clear()
                    break
            if job is None:
                time.sleep(5)
                continue
            try:
                learn_now(job)
            except Exception as e:
                sys.stderr.write("learn failed: %s\n" % e)


def learn_now(job):
    u = find_user_by_id(job["user"])
    if not u:
        return
    current = u.get("memory", "")
    prompt = LEARN_PROMPT.replace("{memory}", current or "(فاضية)").replace("{convo}", job["convo"])
    body = json.dumps({
        "model": job["model"], "stream": False, "format": "json",
        "messages": [{"role": "user", "content": prompt}],
        "options": {"temperature": 0.1, "num_ctx": 8192},
    }).encode()
    upstream = load(CONFIG, {})["upstreams"]["ollama"].rstrip("/")
    r = urllib.request.urlopen(urllib.request.Request(
        upstream + "/api/chat", data=body, headers={"Content-Type": "application/json"}), timeout=300)
    facts = json.loads(json.loads(r.read()).get("message", {}).get("content", "") or "{}").get("facts", [])
    with LOCK:
        data = load(USERS, {"users": []})
        for x in data["users"]:
            if x["id"] != job["user"]:
                continue
            have = [l.strip() for l in x.get("memory", "").splitlines() if l.strip()]
            lower = [l.lower() for l in have]
            added = []
            for f in facts if isinstance(facts, list) else []:
                f = re.sub(r"\s+", " ", str(f)).strip(" -•.")
                if not (4 <= len(f) <= 200) or any(f.lower() in l or l in f.lower() for l in lower):
                    continue
                added.append(f)
                lower.append(f.lower())
                if len(added) >= 5:
                    break
            if added:
                x["memory"] = "\n".join(have + added)[:MAX_MEMORY]
                x["learned"] = {"lines": added, "at": int(time.time())}
        save(USERS, data)


def shared_settings(u):
    """الإعدادات اللي ياخذها أي جهاز بعد الربط."""
    cfg = load(CONFIG, {})
    shared = cfg.get("shared", {})
    out = {}
    if has(u, "servers") and shared.get("kuma_slug"):
        out["kuma_slug"] = shared["kuma_slug"]
    if shared.get("wake_url") and cfg.get("wake_token"):
        out["wake_url"] = shared["wake_url"]
        out["wake_token"] = cfg["wake_token"]
    return out


def mac_address():
    """عنوان كرت الشبكة (للتصحية). السلك أول، وبعده الواي فاي."""
    for dev in ("en0", "en1"):
        try:
            out = subprocess.run(["ifconfig", dev], capture_output=True, text=True, timeout=5).stdout
        except Exception:
            continue
        m = re.search(r"ether ([0-9a-f:]{17})", out)
        if m and "status: active" in out:
            return dev, m.group(1)
    return None, None


WAKER = r'''import os, socket, http.server
MAC = bytes.fromhex(os.environ["MAC"].replace(":", "").replace("-", ""))
PACKET = b"\xff" * 6 + MAC * 16
TOKEN = os.environ["TOKEN"]
class H(http.server.BaseHTTPRequestHandler):
    def do_POST(self):
        if self.path.rstrip("/") != "/wake" or self.headers.get("Authorization") != "Bearer " + TOKEN:
            self.send_response(403); self.end_headers(); return
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
        for addr in ("255.255.255.255", os.environ.get("BROADCAST", "")):
            for port in (9, 7):
                if addr: s.sendto(PACKET, (addr, port))
        self.send_response(200); self.send_header("Content-Type", "application/json"); self.end_headers()
        self.wfile.write(b'{"ok": true}')
    def do_GET(self):
        self.send_response(200); self.end_headers(); self.wfile.write(b'{"waker": true}')
http.server.ThreadingHTTPServer(("", int(os.environ.get("PORT", "9009"))), H).serve_forever()
'''


def find_user_by_id(user_id):
    return next((x for x in load(USERS, {"users": []})["users"] if x["id"] == user_id), None)


def services(u=None):
    """الخدمات اللي في البوابة، ولو فيه مستخدم: اللي مسموحة له بس."""
    names = [k for k, v in load(CONFIG, {}).get("upstreams", {}).items() if v]
    if (u is not None and u.get("claude_key")) or shared_claude_key():
        names.append("claude")
    if u is not None:
        names = [n for n in names if n in SERVICE_PERM and has(u, SERVICE_PERM[n])]
    return sorted(set(names))


# ─────────── الأوامر ───────────

def main():
    os.makedirs(HOME, exist_ok=True)
    cmd = sys.argv[1] if len(sys.argv) > 1 else "serve"

    if cmd == "serve":
        cfg = load(CONFIG, {})
        host, port = cfg.get("host", "0.0.0.0"), int(cfg.get("port", 11500))
        server = ThreadingHTTPServer((host, port), Gateway)
        server.daemon_threads = True
        threading.Thread(target=learn_worker, daemon=True).start()
        threading.Thread(target=brief_worker, daemon=True).start()
        print("البوابة شغالة على %s:%d" % (host, port), flush=True)
        server.serve_forever()

    elif cmd == "version":
        print(VERSION)

    elif cmd == "push-setup":
        if len(sys.argv) < 5:
            print("الاستخدام: python3 gateway.py push-setup ~/Downloads/AuthKey_XXXX.p8 <Key ID> <Team ID>")
            sys.exit(1)
        src = os.path.expanduser(sys.argv[2])
        if not os.path.exists(src):
            print("ما لقيت الملف: " + src)
            sys.exit(1)
        os.makedirs(HOME, exist_ok=True)
        shutil.copyfile(src, os.path.join(HOME, "apns.p8"))
        os.chmod(os.path.join(HOME, "apns.p8"), 0o600)
        with LOCK:
            cfg = load(CONFIG, {})
            cfg["apns"] = {"key_id": sys.argv[3].strip(), "team_id": sys.argv[4].strip(),
                           "topic": "com.imosaab.mosaadi"}
            save(CONFIG, cfg)
        try:
            apns_jwt(cfg["apns"])
            print("تم ✓ التنبيهات جاهزة. افتح التطبيق في الآيفون مرة عشان يسجّل، وبعدين: python3 gateway.py push-test")
        except Exception as e:
            print("الملف ما اشتغل (تأكد إنه ملف .p8 من Apple): %s" % e)

    elif cmd == "push-test":
        data = load(USERS, {"users": []})
        total = 0
        for x in data["users"]:
            if x["role"] == "owner" and x.get("push"):
                total += send_push(x["id"], "مساعدي", "تجربة ✓ التنبيهات شغالة")
        print("وصل لـ %d جهاز." % total if total else
              "ما وصل لأي جهاز. افتح التطبيق في الآيفون (بعد التحديث) واسمح بالتنبيهات، وجرّب مرة ثانية.")

    elif cmd == "wake-setup":
        url = sys.argv[2] if len(sys.argv) > 2 else ""
        dev, mac = mac_address()
        if not mac:
            print("ما لقيت كرت شبكة متصل (en0/en1).")
            sys.exit(1)
        with LOCK:
            cfg = load(CONFIG, {})
            cfg.setdefault("wake_token", secrets.token_urlsafe(24))
            if url:
                cfg.setdefault("shared", {})["wake_url"] = url.rstrip("/")
            save(CONFIG, cfg)
        if dev != "en0":
            print("\n  ⚠️ الماك متصل واي فاي. التصحية تشتغل أضمن بالسلك.\n")
        port = urllib.parse.urlsplit(url).port or 9009 if url else 9009
        print("\n  1) على الماك (مرة وحدة):\n")
        print("      sudo pmset -a womp 1 && sudo pmset -a tcpkeepalive 1\n")
        print("  2) في الـ NAS: Container Manager ← Project ← Create، والصق هذا:\n")
        print("services:\n  mac-waker:\n    image: python:3.12-alpine\n    container_name: mac-waker")
        print("    network_mode: host\n    restart: unless-stopped\n    environment:")
        print('      MAC: "%s"\n      TOKEN: "%s"\n      PORT: "%d"' % (mac, cfg["wake_token"], port))
        print("    command:\n      - python\n      - -c\n      - |")
        for line in WAKER.splitlines():
            print("        " + line)
        print("\n  3) " + ("خلاص ✓ التطبيقات بتاخذ العنوان تلقائياً." if url else
                         "شغّل الأمر مرة ثانية مع عنوان الـ NAS: python3 gateway.py wake-setup http://<NAS>:9009"))
        print("     لما الماك ما يرد، بيطلع لك زر «صحّ الماك» في التطبيق.\n")

    elif cmd == "review":
        # حساب لمراجعة Apple: محادثة بس، ورمز يتكرر لين ينتهي (الافتراضي 14 يوم)
        arg = sys.argv[2] if len(sys.argv) > 2 else "14"
        with LOCK:
            data = load(USERS, {"users": []})
            pairs = load(PAIR, {"codes": []})
            old = [u["id"] for u in data["users"] if u.get("review")]
            data["users"] = [u for u in data["users"] if not u.get("review")]
            pairs["codes"] = [c for c in pairs["codes"] if c.get("user_id") not in old]
            if arg == "off":
                save(USERS, data); save(PAIR, pairs)
                print("انحذف حساب المراجعة ✓")
                sys.exit(0)
            days = int(arg)
            user = {
                "id": secrets.token_hex(4), "name": "Apple Review", "role": "member", "review": True,
                "token_hash": "", "perms": {p: p == "chat" for p in PERMS}, "models": ["*"],
                "disabled": False, "created": now(), "last_used": 0, "paired": False, "claude_limit": 0,
            }
            data["users"].append(user)
            save(USERS, data)
            code = "".join(secrets.choice("0123456789") for _ in range(6))
            pairs["codes"].append({"code": code, "role": "member", "user_id": user["id"],
                                   "expires": now() + days * 86400, "reusable": True})
            save(PAIR, pairs)
        print("\n  رمز المراجعة (يتكرر، يصلح %d يوم):\n\n      %s\n" % (days, code))
        print("  حطه في Review Notes مع عنوان البوابة. بعد الموافقة: python3 gateway.py review off\n")

    elif cmd == "pair":
        code = create_pair_code("owner")
        # الرمز في سطر لحاله وبدون مسافات: لو انطبع جنب كلام عربي، الترمنال في الجوال يقلب ترتيب الأرقام
        print("\n  رمز الربط (يصلح 10 دقايق):\n\n      %s\n" % code)
        print("  في التطبيق: الإعدادات ← البوابة ← اكتب الرمز. يصلح 10 دقايق.\n")

    elif cmd == "brief":
        # يطبع ملخص الصباح الحين (للتجربة). مع "send" يرسله تنبيه بعد.
        b = build_brief()
        print(b["title"] + "\n" + b["text"])
        if len(sys.argv) > 2 and sys.argv[2] == "send":
            save(BRIEF, b)
            n = sum(send_push(x["id"], b["title"], b["text"].replace("\n", " · ")[:180], {"brief": True})
                    for x in load(USERS, {"users": []})["users"] if x.get("push") and has(x, "servers"))
            print("انرسل لـ %d جهاز." % n)

    elif cmd == "merge":
        # يجمع حسابات المالك (لو ربطت أكثر من جهاز قبل 1.5.0) في حساب واحد
        with LOCK:
            data = load(USERS, {"users": []})
            owners = sorted([u for u in data["users"] if u["role"] == "owner" and not u.get("review")],
                            key=lambda u: u.get("created", 0))
            if len(owners) < 2:
                print("عندك حساب مالك واحد بس. ما فيه شي ينجمع.")
                sys.exit(0)
            main = owners[0]
            convs, seen = [], set()
            for u in owners:
                bpath = os.path.join(BACKUPS, re.sub(r"[^0-9a-f]", "", u["id"]) + ".json")
                if os.path.exists(bpath):
                    try:
                        for c in json.load(open(bpath)).get("conversations", []):
                            key = min((m.get("createdAt", 0) for m in c.get("messages", [])), default=0)
                            if key not in seen:
                                seen.add(key)
                                convs.append(c)
                    except ValueError:
                        pass
                if u is main:
                    continue
                main["extra_tokens"] = (main.get("extra_tokens", []) + [u["token_hash"]] + u.get("extra_tokens", []))[-10:]
                lines = [l for l in main.get("memory", "").splitlines() if l.strip()]
                for l in u.get("memory", "").splitlines():
                    if l.strip() and l.strip() not in lines:
                        lines.append(l.strip())
                main["memory"] = "\n".join(lines)[:MAX_MEMORY]
                main["push"] = (main.get("push", []) + [t for t in u.get("push", [])
                                                         if t["token"] not in {x["token"] for x in main.get("push", [])}])[-5:]
                main["display_name"] = main.get("display_name") or u.get("display_name", "")
                main["devices"] = (main.get("devices", []) + [{"name": u.get("device") or u["name"], "at": u.get("created", 0)}])[-10:]
                if os.path.exists(os.path.join(BACKUPS, u["id"] + ".json")):
                    os.remove(os.path.join(BACKUPS, u["id"] + ".json"))
                data["users"].remove(u)
            if convs:
                os.makedirs(BACKUPS, exist_ok=True)
                with open(os.path.join(BACKUPS, main["id"] + ".json"), "w") as f:
                    json.dump({"app": "mosaadi", "version": 1, "exported": int(time.time() * 1000),
                               "device": "gateway", "conversations": convs}, f, ensure_ascii=False)
            save(USERS, data)
        print("تم ✓ صار عندك حساب واحد لـ %d أجهزة. افتح التطبيق في كل جهاز ← الإعدادات ← النسخ والمزامنة ← زامن الحين." % len(owners))

    elif cmd == "users":
        for u in load(USERS, {"users": []})["users"]:
            last = time.strftime("%Y-%m-%d %H:%M", time.localtime(u["last_used"])) if u.get("last_used") else "—"
            state = "موقوف" if u.get("disabled") else ("مالك" if u["role"] == "owner" else "عضو")
            print("%-20s %-6s آخر استخدام: %s" % (u["name"], state, last))

    elif cmd in ("disable", "enable") and len(sys.argv) > 2:
        name = " ".join(sys.argv[2:])
        with LOCK:
            data = load(USERS, {"users": []})
            hits = [u for u in data["users"] if u["name"] == name and u["role"] != "owner"]
            for u in hits:
                u["disabled"] = cmd == "disable"
            save(USERS, data)
        print("تم" if hits else "ما لقيت عضو بهذا الاسم")

    else:
        print(__doc__)


if __name__ == "__main__":
    main()
