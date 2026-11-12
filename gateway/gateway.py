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
"""

VERSION = "1.1.0"
# التحديث بضغطة من التطبيق: البوابة تنزّل نفسها من هنا (غيّره في config.json: "update_url")
DEFAULT_UPDATE_URL = "https://imos3b.github.io/mosaadi/gateway/gateway.py"

import hashlib
import hmac
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
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

HOME = os.path.expanduser("~/Library/Application Support/PrivateAI-Gateway")
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
    out = {k: v for k, v in u.items() if k not in ("token_hash", "claude_key", "claude_usage", "extra_tokens", "device_id")}
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

def create_pair_code(role="owner", user_id=None):
    code = "".join(secrets.choice("0123456789") for _ in range(6))
    with LOCK:
        data = load(PAIR, {"codes": []})
        data["codes"] = [c for c in data["codes"] if c["expires"] > now()]
        data["codes"].append({"code": code, "role": role, "user_id": user_id, "expires": now() + 600})
        save(PAIR, data)
        if user_id:
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
        if match.get("user_id"):
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
            if path == "/gateway/pair-code" and method == "POST":
                if u["role"] != "owner":
                    return self.error(403, "للمالك بس.")
                return self.reply(200, {"code": create_pair_code("owner"), "expires_in": 600})
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

        return self.proxy(method, upstream, rest, data)

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
        self.reply(200, {"user": public(u), "services": services(u), "claude": {
            "shared": bool(shared_claude_key()), "own_key": bool(u.get("claude_key")),
            "limit": None if u["role"] == "owner" or u.get("claude_key") else u.get("claude_limit", CLAUDE_DEFAULT_LIMIT),
            "used": claude_used(u),
        }})

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
        print("البوابة شغالة على %s:%d" % (host, port), flush=True)
        server.serve_forever()

    elif cmd == "version":
        print(VERSION)

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
