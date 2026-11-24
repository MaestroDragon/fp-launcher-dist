#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FP Dragon Launcher - lanzador de juegos para Linux.

- Lee el catálogo de juegos (games.json) del repositorio de GitHub y lo cachea.
- Muestra una tarjeta por juego; si el servidor del juego no responde, la tarjeta
  se queda en gris y no se puede jugar.
- Se actualiza a sí mismo con el manifiesto firmado (UpdateKit: Ed25519 + SHA-256).

No necesita dependencias: solo Python 3 con Tkinter.
"""

import hashlib
import json
import math
import os
import queue
import random
import shutil
import signal
import ssl
import struct
import subprocess
import sys
import tempfile
import threading
import time
import tkinter as tk
import tkinter.font as tkfont
import urllib.error
import urllib.request
import wave
import webbrowser


# --------------------------------------------------------------------------
# Identidad y endpoints
# --------------------------------------------------------------------------
APP_ID = "fp-launcher"
CHANNEL = "stable"
VERSION = "1.3.5"

OWNER = "MaestroDragon"
REPO = "fp-launcher"          # repositorio privado (código, panel, claves)
DIST_REPO = "fp-launcher-dist"  # repositorio público de distribución
BRANCH = "main"
# Todo lo que lee el launcher sale del repo público: tus amigos actualizan sin
# pegar ningún token.
RAW = f"https://raw.githubusercontent.com/{OWNER}/{DIST_REPO}/{BRANCH}"

TITLE = "FP DRAGON LAUNCHER"
SUBTITLE = "Para mis capos de la FP"
STUDIO_URL = "https://dragongamess.wixsite.com/misitio"

PUBLIC_PEM = """-----BEGIN PUBLIC KEY-----
MCowBQYDK2VwAyEAPIT3Vts0jpVNHYSNzrLpYPtESTVPvsZJdOhDO7SmZEo=
-----END PUBLIC KEY-----
"""

USER_AGENT = f"FPLauncher/{VERSION} (Linux; +https://github.com/{OWNER}/{REPO})"

CONFIG_DIR = os.path.join(
    os.environ.get("XDG_CONFIG_HOME") or os.path.expanduser("~/.config"),
    "fp-launcher",
)
CACHE_CATALOG = os.path.join(CONFIG_DIR, "catalog.json")

# Recursos: logo del pie y icono de la ventana.
# Dentro del ejecutable de un solo archivo los assets viajan embebidos y se
# extraen en una carpeta temporal (_MEIPASS).
FROZEN = bool(getattr(sys, "frozen", False))
SCRIPT_ASSET = "fp_launcher.py"
BINARY_ASSET = "fp-launcher"
if FROZEN:
    ASSETS_DIR = os.path.join(
        getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(sys.executable))),
        "assets",
    )
else:
    ASSETS_DIR = os.path.abspath(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "assets")
    )
ASSET_CACHE = os.path.join(CONFIG_DIR, "assets")
LOGO_NAME = "logo.png"
ICON_NAME = "app-icon.png"
GLOW_NAME = "logo-glow.png"
SPARK_NAME = "spark.png"
SPARK_DIM_NAME = "spark-dim.png"

# Sonidos de interfaz (se generan en caché la primera vez).
SFX_DIR = os.path.join(CONFIG_DIR, "sfx")
SAMPLE_RATE = 44100
SFX_PLAYER = None
SFX_FILES = {}

# Token de SOLO LECTURA para el canal de distribución. Nunca se usa el token
# del panel (ese es de escritura y vive en gh-token).
READ_TOKEN_FILE = os.path.join(CONFIG_DIR, "gh-token-read")
GITHUB_API = f"https://api.github.com/repos/{OWNER}/{DIST_REPO}/contents/"

HEALTH_TIMEOUT = 6.0
HEALTH_INTERVAL_MS = 25000

# --------------------------------------------------------------------------
# Paleta neón morada
# --------------------------------------------------------------------------
BG_TOP = "#07030d"
BG_BOTTOM = "#1c0836"
INK = "#f4e9ff"
INK_DIM = "#b9a1dd"
INK_FAINT = "#77618f"
NEON = "#b45cff"
NEON_HOT = "#e6b8ff"
NEON_DEEP = "#7a1fe0"
NEON_LINE = "#3c1069"

CARD = "#160a26"
CARD_OFF = "#0f0916"
CARD_BORDER = "#a855f7"
CARD_BORDER_OFF = "#332445"

GREEN = "#5cf2a8"
AMBER = "#ffc247"
RED = "#ff5c9d"
BTN_OFF = "#221331"

SPARK_COLORS = ["#c084fc", "#a855f7", "#7c3aed", "#e9d5ff", "#9333ea"]

FONT = "DejaVu Sans"
FONT_MONO = "DejaVu Sans Mono"

TICK_MS = 55


# --------------------------------------------------------------------------
# Ed25519 (verificación, sin dependencias externas)
# --------------------------------------------------------------------------
_P = 2 ** 255 - 19
_L = 2 ** 252 + 27742317777372353535851937790883648493


def _inv(x):
    return pow(x, _P - 2, _P)


_D = -121665 * _inv(121666) % _P
_I = pow(2, (_P - 1) // 4, _P)


def _recover_x(y, sign):
    if y >= _P:
        return None
    x2 = (y * y - 1) * _inv(_D * y * y + 1) % _P
    if x2 == 0:
        return None if sign else 0
    x = pow(x2, (_P + 3) // 8, _P)
    if (x * x - x2) % _P != 0:
        x = x * _I % _P
    if (x * x - x2) % _P != 0:
        return None
    if (x & 1) != sign:
        x = _P - x
    return x


_GY = 4 * _inv(5) % _P
_GX = _recover_x(_GY, 0)
_G = (_GX, _GY, 1, _GX * _GY % _P)
_IDENTITY = (0, 1, 1, 0)


def _ed_add(p1, p2):
    x1, y1, z1, t1 = p1
    x2, y2, z2, t2 = p2
    a = (y1 - x1) * (y2 - x2) % _P
    b = (y1 + x1) * (y2 + x2) % _P
    c = t1 * 2 * _D * t2 % _P
    d = z1 * 2 * z2 % _P
    e, f, g, h = b - a, d - c, d + c, b + a
    return (e * f % _P, g * h % _P, f * g % _P, e * h % _P)


def _ed_mul(scalar, point):
    result = _IDENTITY
    while scalar > 0:
        if scalar & 1:
            result = _ed_add(result, point)
        point = _ed_add(point, point)
        scalar >>= 1
    return result


def _ed_encode(point):
    x, y, z, _ = point
    zi = _inv(z)
    x = x * zi % _P
    y = y * zi % _P
    return int(y | ((x & 1) << 255)).to_bytes(32, "little")


def ed25519_verify(public_key, signature, message):
    """True si `signature` es válida para `message` con `public_key` (32 bytes)."""
    if len(public_key) != 32 or len(signature) != 64:
        return False
    r_enc = signature[:32]
    s = int.from_bytes(signature[32:], "little")
    if s >= _L:
        return False
    y = int.from_bytes(public_key, "little") & ((1 << 255) - 1)
    sign = public_key[31] >> 7
    x = _recover_x(y, sign)
    if x is None:
        return False
    a_point = (x, y, 1, x * y % _P)
    h = hashlib.sha512(r_enc + public_key + message).digest()
    h = int.from_bytes(h, "little") % _L
    check = _ed_add(_ed_mul(s, _G), _ed_mul(_L - h if h else 0, a_point))
    return _ed_encode(check) == r_enc


def pem_to_raw_public_key(pem):
    """Extrae los 32 bytes de una clave pública Ed25519 en formato SPKI/PEM."""
    import base64

    lines = [ln.strip() for ln in pem.strip().splitlines()]
    body = "".join(ln for ln in lines if not ln.startswith("-----"))
    der = base64.b64decode(body)
    # SPKI Ed25519: 30 2a 30 05 06 03 2b 65 70 03 21 00 || 32 bytes
    if len(der) == 44 and der[:12] == bytes.fromhex("302a300506032b6570032100"):
        return der[12:]
    raise ValueError("Clave pública no es Ed25519/SPKI")


def canonical_json(value):
    """Igual que canonicalJson() del UpdateKit: claves ordenadas, sin espacios."""
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (int, float)):
        if isinstance(value, float) and value.is_integer():
            return str(int(value))
        return json.dumps(value)
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False)
    if isinstance(value, list):
        return "[" + ",".join(canonical_json(v) for v in value) + "]"
    if isinstance(value, dict):
        items = sorted(value.items(), key=lambda kv: kv[0])
        return "{" + ",".join(
            json.dumps(k, ensure_ascii=False) + ":" + canonical_json(v)
            for k, v in items
        ) + "}"
    raise TypeError(f"canonical_json: tipo no soportado {type(value)!r}")


# --------------------------------------------------------------------------
# Red
# --------------------------------------------------------------------------
def _ssl_context():
    return ssl.create_default_context()


def http_get(url, timeout=10.0, max_bytes=8 * 1024 * 1024):
    req = urllib.request.Request(
        url, headers={"User-Agent": USER_AGENT, "Cache-Control": "no-cache"}
    )
    with urllib.request.urlopen(req, timeout=timeout, context=_ssl_context()) as resp:
        data = resp.read(max_bytes + 1)
        if len(data) > max_bytes:
            raise ValueError("respuesta demasiado grande")
        return data


class PrivateRepoError(RuntimeError):
    """El repositorio es privado y falta (o no vale) el código de acceso."""


def github_token():
    """Token de solo lectura del canal público (opcional)."""
    token = (os.environ.get("FPL_TOKEN_READ") or "").strip()
    if token:
        return token
    try:
        with open(READ_TOKEN_FILE, "r", encoding="utf-8") as fh:
            return fh.read().strip()
    except Exception:
        return ""


def save_github_token(token):
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(READ_TOKEN_FILE, "w", encoding="utf-8") as fh:
            fh.write(token.strip())
        os.chmod(READ_TOKEN_FILE, 0o600)
        return True
    except Exception:
        return False


def _api_get(repo_path, token, timeout, max_bytes):
    req = urllib.request.Request(
        GITHUB_API + repo_path + "?ref=" + BRANCH,
        headers={
            "Authorization": f"Bearer {token}",
            "Accept": "application/vnd.github.raw",
            "User-Agent": USER_AGENT,
            "X-GitHub-Api-Version": "2022-11-28",
            "Cache-Control": "no-cache",
        },
    )
    with urllib.request.urlopen(req, timeout=timeout, context=_ssl_context()) as resp:
        data = resp.read(max_bytes + 1)
    if len(data) > max_bytes:
        raise ValueError("respuesta demasiado grande")
    return data


def fetch_repo_file(repo_path, timeout=12.0, max_bytes=8 * 1024 * 1024):
    """Lee un archivo del repo; si es privado, usa el código de acceso."""
    try:
        return http_get(RAW + "/" + repo_path, timeout=timeout, max_bytes=max_bytes)
    except urllib.error.HTTPError as exc:
        if exc.code not in (401, 403, 404):
            raise
    token = github_token()
    if not token:
        raise PrivateRepoError("el repositorio es privado y falta el código de acceso")
    try:
        return _api_get(repo_path, token, timeout, max_bytes)
    except urllib.error.HTTPError as exc:
        if exc.code in (401, 403, 404):
            raise PrivateRepoError("código de acceso no válido o sin permiso")
        raise


def check_health(game):
    """True si el servidor del juego responde."""
    base = (game.get("url") or "").strip().rstrip("/")
    if not base:
        return False
    path = game.get("health_path") or "/api/health"
    if not path.startswith("/"):
        path = "/" + path
    try:
        req = urllib.request.Request(
            base + path, headers={"User-Agent": USER_AGENT, "Cache-Control": "no-cache"}
        )
        with urllib.request.urlopen(
            req, timeout=HEALTH_TIMEOUT, context=_ssl_context()
        ) as resp:
            return 200 <= resp.status < 400
    except Exception:
        return False


# --------------------------------------------------------------------------
# Utilidades
# --------------------------------------------------------------------------
def parse_version(text):
    core = str(text).strip().lstrip("vV").split("+")[0].split("-")[0]
    parts = []
    for piece in core.split("."):
        try:
            parts.append(int(piece))
        except ValueError:
            parts.append(0)
    while len(parts) < 3:
        parts.append(0)
    return tuple(parts[:3])


def load_cached_catalog():
    try:
        with open(CACHE_CATALOG, "r", encoding="utf-8") as fh:
            return json.load(fh)
    except Exception:
        return None


def save_cached_catalog(catalog):
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(CACHE_CATALOG, "w", encoding="utf-8") as fh:
            json.dump(catalog, fh, ensure_ascii=False, indent=2)
    except Exception:
        pass


def hex_mix(a, b, t):
    """Mezcla lineal de dos colores hex (#rrggbb)."""
    a = a.lstrip("#")
    b = b.lstrip("#")
    out = []
    for i in range(3):
        ca = int(a[i * 2:i * 2 + 2], 16)
        cb = int(b[i * 2:i * 2 + 2], 16)
        out.append(int(round(ca + (cb - ca) * t)))
    return "#%02x%02x%02x" % tuple(max(0, min(255, c)) for c in out)


# --------------------------------------------------------------------------
# Sonido y recursos
# --------------------------------------------------------------------------
def _find_player():
    for candidate in ("paplay", "pw-play", "aplay", "ffplay"):
        path = shutil.which(candidate)
        if path:
            return path
    return None


def _synth(kind):
    """Genera las muestras de un efecto: barrido de senos con envolvente."""
    specs = {
        # duración, frecuencia según el avance (0..1), caída
        "open": (0.55, lambda p: 240 + 760 * p * p, 1.3),
        "close": (0.42, lambda p: 620 - 430 * p, 1.6),
        "click": (0.075, lambda p: 1180 - 180 * p, 2.4),
    }
    duration, freq_at, decay = specs[kind]
    total = int(SAMPLE_RATE * duration)
    phase = 0.0
    samples = []
    for index in range(total):
        t = index / SAMPLE_RATE
        progress = t / duration
        phase += 2.0 * math.pi * freq_at(progress) / SAMPLE_RATE
        attack = min(1.0, t / 0.012) if duration > 0.1 else 1.0
        envelope = attack * (1.0 - progress) ** decay
        wave_shape = (
            math.sin(phase)
            + 0.28 * math.sin(2.0 * phase)
            + 0.10 * math.sin(3.0 * phase)
        )
        value = 0.22 * envelope * wave_shape
        samples.append(int(max(-1.0, min(1.0, value)) * 32767))
    return samples


def ensure_sfx():
    """Crea los WAV en la caché la primera vez y devuelve {nombre: ruta}."""
    global SFX_PLAYER
    if SFX_FILES:
        return SFX_FILES
    if SFX_PLAYER is None:
        SFX_PLAYER = _find_player()
    if not SFX_PLAYER:
        return {}
    try:
        os.makedirs(SFX_DIR, exist_ok=True)
    except Exception:
        return {}
    for kind in ("open", "close", "click"):
        path = os.path.join(SFX_DIR, kind + ".wav")
        if not os.path.isfile(path):
            try:
                samples = _synth(kind)
                with wave.open(path, "wb") as fh:
                    fh.setnchannels(1)
                    fh.setsampwidth(2)
                    fh.setframerate(SAMPLE_RATE)
                    fh.writeframes(struct.pack(f"<{len(samples)}h", *samples))
            except Exception:
                continue
        if os.path.isfile(path):
            SFX_FILES[kind] = path
    return SFX_FILES


def play_sound(kind):
    """Reproduce un efecto sin bloquear la interfaz."""
    path = ensure_sfx().get(kind)
    if not path or not SFX_PLAYER:
        return
    args = [SFX_PLAYER]
    if SFX_PLAYER.endswith("ffplay"):
        args += ["-nodisp", "-autoexit", "-loglevel", "quiet"]
    args.append(path)
    try:
        subprocess.Popen(args, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    except Exception:
        pass


def asset_path(name):
    """Busca el recurso junto al launcher, en caché o en el repositorio."""
    for candidate in (
        os.path.join(ASSETS_DIR, name),
        os.path.join(ASSET_CACHE, name),
    ):
        if os.path.isfile(candidate):
            return candidate
    try:
        data = fetch_repo_file("assets/" + name, timeout=8)
        os.makedirs(ASSET_CACHE, exist_ok=True)
        cached = os.path.join(ASSET_CACHE, name)
        with open(cached, "wb") as fh:
            fh.write(data)
        return cached
    except Exception:
        return None


def install_desktop_icon():
    """Deja el icono en el tema del usuario para que el archivo lo muestre."""
    home = os.path.expanduser("~")
    share = os.path.join(home, ".local", "share")
    source = asset_path(ICON_NAME)
    if not source:
        return
    try:
        with open(source, "rb") as fh:
            icon_data = fh.read()
    except Exception:
        return

    icon_dir = os.path.join(share, "icons", "hicolor", "256x256", "apps")
    icon_path = os.path.join(icon_dir, "fp-launcher.png")
    try:
        os.makedirs(icon_dir, exist_ok=True)
        current = b""
        if os.path.isfile(icon_path):
            with open(icon_path, "rb") as fh:
                current = fh.read()
        if current != icon_data:
            with open(icon_path, "wb") as fh:
                fh.write(icon_data)
    except Exception:
        pass

    executable = os.path.abspath(sys.executable)
    if FROZEN:
        command = f'"{executable}"'
    else:
        command = f'"{executable}" "{os.path.abspath(__file__)}"'
    entry = (
        "[Desktop Entry]\n"
        "Type=Application\n"
        "Version=1.0\n"
        "Name=FP Dragon Launcher\n"
        "Comment=Launcher de juegos de la FP\n"
        f"Exec={command}\n"
        "Icon=fp-launcher\n"
        "Terminal=false\n"
        "Categories=Game;\n"
        "StartupWMClass=fp-launcher\n"
    )
    desktop_dir = os.path.join(share, "applications")
    desktop_path = os.path.join(desktop_dir, "fp-launcher.desktop")
    try:
        os.makedirs(desktop_dir, exist_ok=True)
        current = ""
        if os.path.isfile(desktop_path):
            with open(desktop_path, "r", encoding="utf-8") as fh:
                current = fh.read()
        if current != entry:
            with open(desktop_path, "w", encoding="utf-8") as fh:
                fh.write(entry)
            os.chmod(desktop_path, 0o755)
    except Exception:
        pass


def load_photo(path, height=None, width=None):
    """Carga un PNG escalado (usa Pillow si está; si no, Tk a pelo)."""
    if not path:
        return None
    try:
        from PIL import Image, ImageTk

        image = Image.open(path).convert("RGBA")
        if height:
            size = (max(1, round(image.width * height / image.height)), height)
        elif width:
            size = (width, max(1, round(image.height * width / image.width)))
        else:
            size = image.size
        resample = getattr(Image, "LANCZOS", Image.BICUBIC)
        return ImageTk.PhotoImage(image.resize(size, resample))
    except Exception:
        try:
            photo = tk.PhotoImage(file=path)
            if height:
                photo = photo.subsample(max(1, round(photo.height() / height)))
            return photo
        except Exception:
            return None


# --------------------------------------------------------------------------
# Interfaz
# --------------------------------------------------------------------------
class Spark:
    """Chispa morada que sube y se desenfoca."""

    __slots__ = ("x", "y", "r", "speed", "drift", "color", "photo")

    def __init__(self, x, y, r, speed, drift, color, photo=None):
        self.x = x
        self.y = y
        self.r = r
        self.speed = speed
        self.drift = drift
        self.color = color
        self.photo = photo


class Launcher(tk.Tk):
    STATES = ("unknown", "online", "offline", "maintenance")

    def __init__(self):
        super().__init__()
        self.title(TITLE)
        self.configure(bg=BG_TOP)
        self.geometry("1080x680")
        self.minsize(960, 620)
        # Ventana normal: se minimiza, se maximiza y se apila como cualquier
        # app (una ventana sin marco del sistema flotaría por encima de todo).
        self._fullscreen = False
        self._minimized = False
        self._windowed_geometry = "1080x680"
        screen_w = self.winfo_screenwidth()
        screen_h = self.winfo_screenheight()
        self.geometry(
            f"1080x680+{max(0, (screen_w - 1080) // 2)}"
            f"+{max(0, (screen_h - 680) // 2)}"
        )
        try:
            signal.signal(signal.SIGUSR1, self._on_wake)
        except Exception:
            pass

        self.events = queue.Queue()
        self.games = []
        self.cards = {}
        self.states = {}
        self.busy = False
        self._alive = True
        self._layout_job = None
        self._tick_job = None
        self._chrome_buttons = []
        self._card_widgets = []
        self._sparks = []
        self._spark_items = []
        self._placeholder_text = "Cargando catálogo…"
        self._logo_photo = None
        self._icon_photo = None
        self._closing = False
        self._alpha_ok = True
        self._updating = False
        self._update_manifest = None
        self._update_target = None
        self._update_error = None
        self._countdown = 0
        self._count_item = None
        self._progress_item = None
        self._confirming = False
        self._pending_manifest = None
        self._overlay_widgets = []
        self._logo_hover = False

        self.protocol("WM_DELETE_WINDOW", self._close)

        self.canvas = tk.Canvas(
            self, bg=BG_TOP, highlightthickness=0, bd=0, takefocus=0
        )
        self.canvas.pack(fill="both", expand=True)

        self.title_font = tkfont.Font(family=FONT, size=30, weight="bold")
        self.sub_font = tkfont.Font(family=FONT, size=12)
        self.card_title_font = tkfont.Font(family=FONT, size=17, weight="bold")
        self.card_sub_font = tkfont.Font(family=FONT, size=9)
        self.card_status_font = tkfont.Font(family=FONT, size=10, weight="bold")
        self.card_url_font = tkfont.Font(family=FONT_MONO, size=7)
        self.btn_font = tkfont.Font(family=FONT, size=9, weight="bold")
        self.card_btn_font = tkfont.Font(family=FONT, size=10, weight="bold")
        self.small_font = tkfont.Font(family=FONT, size=8)

        self._set_alpha(0.0)
        self._load_assets()
        self._build_chrome()
        self._build_sparks()

        self.canvas.bind("<Configure>", self._on_resize)
        self.bind("<F11>", lambda _e: self._toggle_fullscreen())
        self.bind("<Escape>", self._exit_fullscreen)

        cached = load_cached_catalog()
        if cached and cached.get("games"):
            self.render(cached)
        else:
            self._draw_cards()

        self.after(120, self.refresh_catalog_async)
        self.after(200, self._drain_events)
        self.after(1500, self.health_tick)
        self.after(3000, self.auto_check_updates)
        self._tick()
        self._show_on_top()
        self.after(900, lambda: threading.Thread(
            target=install_desktop_icon, daemon=True).start())
        self._fade(0.0, 1.0, 16, 22)
        # Red de seguridad: si el WM acepta -alpha pero no compone, no dejar el
        # launcher invisible.
        self.after(1400, lambda: self._set_alpha(1.0))

    # -- sonido, logo y fundido -------------------------------------------
    def _load_assets(self):
        ensure_sfx()
        logo = asset_path(LOGO_NAME)
        self._logo_photo = load_photo(logo, height=66)
        self._logo_box = self._logo_glyph_box(self._logo_photo)
        self._logo_glow_photo = load_photo(asset_path(GLOW_NAME), height=210)
        self._spark_photos = []
        for name in (SPARK_NAME, SPARK_DIM_NAME):
            photo = load_photo(asset_path(name), width=26)
            if photo is not None:
                self._spark_photos.append(photo)
                try:
                    self._spark_photos.append(photo.subsample(2))
                except Exception:
                    pass
        icon = load_photo(asset_path(ICON_NAME), width=128)
        if icon is not None:
            self._icon_photo = icon
            try:
                self.iconphoto(True, icon)
            except Exception:
                pass

    @staticmethod
    def _logo_glyph_box(photo):
        """Caja de los píxeles visibles del logo (el PNG trae margen)."""
        if photo is None:
            return (0, 0, 0, 0)
        width, height = photo.width(), photo.height()
        min_x, min_y, max_x, max_y = width, height, -1, -1
        for y in range(height):
            for x in range(width):
                try:
                    if photo.transparency_get(x, y):
                        continue
                except Exception:
                    pass
                if photo.get(x, y) == (0, 0, 0):
                    continue
                if x < min_x:
                    min_x = x
                if y < min_y:
                    min_y = y
                if x > max_x:
                    max_x = x
                if y > max_y:
                    max_y = y
        if max_x < 0:
            return (0, 0, width, height)
        return (min_x, min_y, max_x, max_y)

    def _set_alpha(self, value):
        try:
            self.wm_attributes("-alpha", value)
            return True
        except tk.TclError:
            self._alpha_ok = False
            return False

    def _fade(self, start, end, steps, delay, on_done=None, step=0):
        if not self._alpha_ok:
            if on_done:
                on_done()
            return
        progress = step / max(1, steps)
        eased = 1.0 - (1.0 - progress) ** 2
        self._set_alpha(max(0.0, min(1.0, start + (end - start) * eased)))
        if step >= steps:
            if on_done:
                on_done()
            return
        self.after(
            delay, lambda: self._fade(start, end, steps, delay, on_done, step + 1)
        )

    def _close(self):
        if self._closing:
            return
        self._closing = True
        play_sound("close")
        if self._layout_job:
            try:
                self.after_cancel(self._layout_job)
            except Exception:
                pass
            self._layout_job = None
        self._fade(1.0, 0.0, 12, 18, on_done=self._finish_close)

    def _finish_close(self):
        self._alive = False
        release_instance()
        try:
            self.destroy()
        except Exception:
            pass

    # -- chasis (botones fijos) -------------------------------------------
    def _sounded(self, callback):
        def wrapped():
            play_sound("click")
            callback()
        return wrapped

    def _neon_button(self, master, text, command, font, width=None, height=None):
        btn = tk.Button(
            master,
            text=text,
            command=self._sounded(command),
            bd=0,
            relief="flat",
            highlightthickness=0,
            font=font,
            fg=INK,
            bg="#251139",
            activebackground=NEON_DEEP,
            activeforeground="#ffffff",
            disabledforeground=INK_FAINT,
            cursor="hand2",
            padx=2,
            pady=6,
        )
        return btn

    def _build_chrome(self):
        self.btn_update = self._neon_button(
            self.canvas, "Actualizar launcher", self.check_updates_clicked,
            self.btn_font,
        )
        self.btn_catalog = self._neon_button(
            self.canvas, "Buscar estado server", self.search_servers, self.btn_font,
        )
        self._chrome_buttons = [self.btn_catalog, self.btn_update]
        self.btn_update_win = self.canvas.create_window(
            0, 0, window=self.btn_update, anchor="w", width=164, height=32,
            tags=("ui",),
        )
        self.btn_catalog_win = self.canvas.create_window(
            0, 0, window=self.btn_catalog, anchor="w", width=164, height=32,
            tags=("ui",),
        )
        # El logo del pie es el botón que lleva a la web del estudio.
        self.canvas.tag_bind("logo", "<Button-1>", lambda _e: self._logo_clicked())
        self.canvas.tag_bind("logo", "<Enter>", self._logo_enter)
        self.canvas.tag_bind("logo", "<Leave>", self._logo_leave)

    # -- chispas -----------------------------------------------------------
    def _build_sparks(self):
        self._sparks = []
        self._spark_items = []
        photos = getattr(self, "_spark_photos", [])
        if not photos:
            return
        for _ in range(40):
            self._sparks.append(
                Spark(
                    random.uniform(0, 1080),
                    random.uniform(0, 680),
                    random.uniform(0.6, 1.5),
                    random.uniform(0.12, 0.55),
                    random.uniform(-0.09, 0.09),
                    random.choice(SPARK_COLORS),
                    random.choice(photos),
                )
            )
        for spark in self._sparks:
            item = self.canvas.create_image(
                0, 0, image=spark.photo, tags=("spark",)
            )
            self._spark_items.append(item)
        self._lower_sparks()

    def _lower_sparks(self):
        """Las chispas van por detrás de la barra y de las tarjetas."""
        if not self.canvas.find_withtag("spark"):
            return
        if self.canvas.find_withtag("chrome"):
            self.canvas.tag_lower("spark", "chrome")

    def _tick(self):
        if not self._alive:
            return
        height = self.canvas.winfo_height() or 680
        width = self.canvas.winfo_width() or 1080
        photos = getattr(self, "_spark_photos", [])
        for spark, item in zip(self._sparks, self._spark_items):
            spark.y -= spark.speed
            spark.x += spark.drift
            if spark.y < -30 or spark.x < -30 or spark.x > width + 30:
                spark.y = height + random.uniform(20, 200)
                spark.x = random.uniform(0, max(width, 1))
                spark.speed = random.uniform(0.12, 0.55)
                spark.drift = random.uniform(-0.09, 0.09)
                if photos:
                    spark.photo = random.choice(photos)
                    self.canvas.itemconfigure(item, image=spark.photo)
            self.canvas.coords(item, spark.x, spark.y)
        self._tick_job = self.after(TICK_MS, self._tick)

    # -- disposición -------------------------------------------------------
    def _on_resize(self, _event=None):
        if self._layout_job:
            try:
                self.after_cancel(self._layout_job)
            except Exception:
                pass
        self._layout_job = self.after(40, self._relayout)

    def _relayout(self):
        self._layout_job = None
        if not self._alive:
            return
        self._draw_gradient()
        self._layout_chrome()
        if self._updating:
            self._draw_update_overlay(self._update_manifest or {})
        elif self._confirming:
            self._draw_confirm_overlay(self._pending_manifest or {})
        else:
            self._draw_cards()

    def _draw_gradient(self):
        self.canvas.delete("grad")
        width = self.canvas.winfo_width() or 1080
        height = self.canvas.winfo_height() or 680
        steps = 64
        band = height / steps
        for i in range(steps):
            color = hex_mix(BG_TOP, BG_BOTTOM, (i / (steps - 1)) ** 1.5)
            self.canvas.create_rectangle(
                0, i * band, width, (i + 1) * band + 1,
                fill=color, outline="", tags=("grad",),
            )
        self.canvas.tag_lower("grad")

    def _layout_chrome(self):
        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()
        if width < 200 or height < 200:
            return
        self._set_chrome_visible(not self._updating)

        update_x = width - 44 - 164
        self.canvas.coords(self.btn_update_win, update_x, height - 46)
        self.canvas.coords(self.btn_catalog_win, update_x - 164 - 8, height - 46)

        self.canvas.delete("chrome")
        cx = width / 2

        top = 0

        # Halo neón tras el título (desenfoque simulado con capas).
        title_w = self.title_font.measure(TITLE)
        self.canvas.create_oval(
            cx - title_w * 0.62, top + 34, cx + title_w * 0.62, top + 92,
            fill="#4a1080", outline="", stipple="gray12", tags=("chrome",),
        )
        self.canvas.create_oval(
            cx - title_w * 0.54, top + 42, cx + title_w * 0.54, top + 84,
            fill="#7a1fd0", outline="", stipple="gray25", tags=("chrome",),
        )
        self.canvas.create_text(
            cx, top + 62, text=TITLE, fill=INK, font=self.title_font,
            tags=("chrome",),
        )
        self.canvas.create_text(
            cx, top + 98, text=SUBTITLE, fill=NEON_HOT, font=self.sub_font,
            tags=("chrome",),
        )

        # Línea futurista bajo la cabecera.
        self.canvas.create_line(
            44, top + 132, width - 44, top + 132, fill=NEON_LINE, width=1,
            tags=("chrome",),
        )
        self.canvas.create_line(
            cx - 130, top + 132, cx + 130, top + 132, fill=NEON, width=2,
            tags=("chrome",),
        )
        self.canvas.create_text(
            cx, top + 148, text="S E L E C C I O N A   T U   J U E G O",
            fill=INK_FAINT, font=tkfont.Font(family=FONT, size=7), tags=("chrome",),
        )

        # Pie.
        self.canvas.create_line(
            44, height - 88, width - 44, height - 88,
            fill=NEON_LINE, width=1, tags=("chrome",),
        )
        # Logo de la casa abajo a la izquierda; al pulsarlo se abre la web.
        logo_w = 0
        if self._logo_photo is not None:
            logo_w = self._logo_photo.width()
            self.canvas.create_image(
                30, height - 12, image=self._logo_photo, anchor="sw",
                tags=("chrome", "logo"),
            )
            if self._logo_hover and not (self._updating or self._confirming):
                self._draw_logo_glow()
        self.canvas.create_text(
            30 + logo_w + 16, height - 18, text="Listo", fill=INK_FAINT,
            font=self.small_font, anchor="w", tags=("chrome", "status"),
        )
        self.canvas.create_text(
            width - 28, height - 18, text=f"v{VERSION}", fill=INK_FAINT,
            font=self.small_font, anchor="e", tags=("chrome",),
        )
        # El estado se actualiza en caliente.
        self.status_item = self.canvas.find_withtag("status")
        self._lower_sparks()

    def set_status(self, text):
        items = self.canvas.find_withtag("status")
        if not items:
            return
        self.canvas.itemconfigure(items[0], text=text)

    def _round_rect(self, x1, y1, x2, y2, r, **kwargs):
        r = min(r, (x2 - x1) / 2, (y2 - y1) / 2)
        points = [
            x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r,
            x2, y2 - r, x2, y2, x2 - r, y2, x1 + r, y2,
            x1, y2, x1, y2 - r, x1, y1 + r, x1, y1,
        ]
        return self.canvas.create_polygon(
            points, smooth=True, splinesteps=18, **kwargs
        )

    # -- catálogo ----------------------------------------------------------
    def show_placeholder(self, text):
        self._placeholder_text = text
        self._draw_cards()

    def render(self, catalog):
        self.games = catalog.get("games") or []
        for game in self.games:
            gid = game.get("id")
            if game.get("status") == "maintenance":
                self.states[gid] = "maintenance"
            else:
                self.states[gid] = "unknown"
        self._draw_cards()

    def _draw_cards(self):
        self.canvas.delete("card")
        for widget in self._card_widgets:
            try:
                widget.destroy()
            except Exception:
                pass
        self._card_widgets = []
        self.cards = {}

        width = self.canvas.winfo_width()
        height = self.canvas.winfo_height()
        if width < 200 or height < 200:
            return

        if not self.games:
            self.canvas.create_text(
                width / 2, height / 2, text=self._placeholder_text,
                fill=INK_DIM, font=tkfont.Font(family=FONT, size=11),
                justify="center", tags=("card",),
            )
            return

        margin = 44
        top = 172
        bottom = height - 108
        gap = 20
        cols = max(1, min(3, len(self.games)))
        rows = int(math.ceil(len(self.games) / cols))
        card_w = (width - 2 * margin - gap * (cols - 1)) / cols
        card_h = max(230, (bottom - top - gap * (rows - 1)) / rows)

        for index, game in enumerate(self.games):
            col = index % cols
            row = index // cols
            x1 = margin + col * (card_w + gap)
            y1 = top + row * (card_h + gap)
            x2 = x1 + card_w
            y2 = y1 + card_h
            self._build_card(game, x1, y1, x2, y2)

    def _build_card(self, game, x1, y1, x2, y2):
        gid = game.get("id") or str(len(self.cards))
        tags = ("card",)
        bg = self._round_rect(
            x1, y1, x2, y2, 14, fill=CARD, outline=CARD_BORDER, width=2, tags=tags,
        )
        inner_w = max(80, (x2 - x1) - 36)
        title = self.canvas.create_text(
            x1 + 18, y1 + 18, text=game.get("title", "Juego"), fill=INK,
            font=self.card_title_font, anchor="nw", width=inner_w, tags=tags,
        )
        subtitle = self.canvas.create_text(
            x1 + 18, y1 + 52, text=game.get("subtitle", ""), fill=INK_DIM,
            font=self.card_sub_font, anchor="nw", width=inner_w, tags=tags,
        )
        divider = self.canvas.create_line(
            x1 + 18, y1 + 96, x2 - 18, y1 + 96, fill=NEON_LINE, width=1,
            tags=tags,
        )
        status = self.canvas.create_text(
            x1 + 18, y1 + 110, text="●  Comprobando…", fill=NEON_HOT,
            font=self.card_status_font, anchor="nw", tags=tags,
        )
        note = self.canvas.create_text(
            x1 + 18, y1 + 138, text=game.get("note", ""), fill=INK_DIM,
            font=self.card_sub_font, anchor="nw", width=inner_w, tags=tags,
        )
        url = self.canvas.create_text(
            x1 + 18, y2 - 66, text=(game.get("url") or "sin dirección"),
            fill=INK_FAINT, font=self.card_url_font, anchor="sw", width=inner_w,
            tags=tags,
        )
        button = tk.Button(
            self.canvas, text="COMPROBANDO…",
            command=lambda g=game: self._card_clicked(g), bd=0, relief="flat",
            highlightthickness=0, font=self.card_btn_font, fg="#8d7aa6",
            bg="#2a1a42", activebackground=NEON_DEEP, activeforeground="#ffffff",
            disabledforeground="#6f5b8a", cursor="arrow", padx=6, pady=6,
        )
        self._card_widgets.append(button)
        window = self.canvas.create_window(
            (x1 + x2) / 2, y2 - 16, window=button, anchor="s",
            width=int(inner_w), height=38, tags=tags,
        )
        self.cards[gid] = {
            "game": game,
            "items": {
                "bg": bg, "title": title, "subtitle": subtitle,
                "divider": divider, "status": status, "note": note, "url": url,
            },
            "button": button,
            "window": window,
        }
        self._paint(gid)

    def _card_clicked(self, game):
        play_sound("click")
        gid = game.get("id")
        state = self.states.get(gid, "unknown")
        if state == "online":
            self.play(game)
        elif state == "offline":
            self.retry_one(game)

    # -- pintura según estado ---------------------------------------------
    def _paint(self, gid):
        card = self.cards.get(gid)
        if card is None:
            return
        game = card["game"]
        items = card["items"]
        state = self.states.get(gid, "unknown")
        button = card["button"]

        if state == "online":
            bg, border = CARD, CARD_BORDER
            title_fg, dim_fg = INK, INK_DIM
            status_text, status_fg = "●  SERVIDOR ACTIVO", GREEN
            button_text, btn_bg, btn_fg = "JUGAR", NEON_DEEP, "#ffffff"
            button_state, cursor = "normal", "hand2"
            note_text = game.get("online_note") or game.get("note", "")
        elif state == "offline":
            bg, border = CARD_OFF, CARD_BORDER_OFF
            title_fg, dim_fg = INK_FAINT, INK_FAINT
            status_text, status_fg = "●  SERVIDOR APAGADO", RED
            button_text, btn_bg, btn_fg = "REINTENTAR", "#2a1740", INK_DIM
            button_state, cursor = "normal", "hand2"
            note_text = game.get("offline_note") or "El servidor está apagado."
        elif state == "maintenance":
            bg, border = CARD_OFF, CARD_BORDER_OFF
            title_fg, dim_fg = INK_FAINT, INK_FAINT
            status_text, status_fg = "●  EN MANTENIMIENTO", AMBER
            button_text, btn_bg, btn_fg = "EN MANTENIMIENTO", BTN_OFF, "#6f5b8a"
            button_state, cursor = "disabled", "arrow"
            note_text = game.get("note", "")
        else:
            bg, border = CARD, CARD_BORDER_OFF
            title_fg, dim_fg = INK, INK_DIM
            status_text, status_fg = "●  COMPROBANDO…", NEON_HOT
            button_text, btn_bg, btn_fg = "COMPROBANDO…", "#2a1a42", "#8d7aa6"
            button_state, cursor = "disabled", "arrow"
            note_text = game.get("note", "")

        self.canvas.itemconfigure(items["bg"], fill=bg, outline=border)
        self.canvas.itemconfigure(items["title"], fill=title_fg)
        self.canvas.itemconfigure(items["subtitle"], fill=dim_fg)
        self.canvas.itemconfigure(items["divider"], fill=NEON_LINE if
                                  state in ("online", "unknown") else border)
        self.canvas.itemconfigure(
            items["status"], text=status_text, fill=status_fg
        )
        self.canvas.itemconfigure(items["note"], text=note_text, fill=dim_fg)
        self.canvas.itemconfigure(items["url"], fill=dim_fg)

        button.configure(
            text=button_text, state=button_state, bg=btn_bg, fg=btn_fg,
            cursor=cursor, activebackground=NEON_DEEP, activeforeground="#ffffff",
        )

    def refresh_catalog_async(self):
        if self.busy:
            return
        self.busy = True
        self.set_status("Actualizando catálogo…")
        threading.Thread(target=self._refresh_catalog_worker, daemon=True).start()

    def search_servers(self):
        """Botón «Buscar estado server»: recarga el catálogo y sondea la salud."""
        self.refresh_catalog_async()
        self.set_status("Buscando estado de los servidores…")
        threading.Thread(target=self._health_worker, daemon=True).start()

    def _refresh_catalog_worker(self):
        try:
            catalog = json.loads(
                fetch_repo_file("launcher/games.json", timeout=12).decode("utf-8")
            )
            if not isinstance(catalog, dict) or not isinstance(catalog.get("games"), list):
                raise ValueError("catálogo con formato inesperado")
            save_cached_catalog(catalog)
            self.events.put(("catalog", catalog))
        except PrivateRepoError as exc:
            self.events.put(("need_token", str(exc)))
        except Exception as exc:  # noqa: BLE001
            self.events.put(("error", f"No se pudo actualizar el catálogo: {exc}"))

    def prompt_token(self, reason=""):
        """Pide una vez el código de acceso cuando el repo es privado."""
        self.set_status("Repositorio privado: hace falta el código de acceso")
        code = self.ask_text(
            "Código de acceso",
            "No se pudo leer el canal de actualizaciones.\n\n"
            "Pega un token de SOLO LECTURA (se guarda solo en tu PC):",
        )
        if not code or not code.strip():
            self.show_placeholder(
                "Hace falta el código de acceso al repositorio.\n"
                "Pulsa «Buscar estado server» para introducirlo."
            )
            return
        if save_github_token(code):
            self.set_status("Código guardado. Reintentando…")
            self.refresh_catalog_async()
        else:
            self.show_error("No se pudo guardar el código de acceso.")

    # -- salud de los servidores -----------------------------------------
    def health_tick(self):
        if not self._alive:
            return
        threading.Thread(target=self._health_worker, daemon=True).start()
        self.after(HEALTH_INTERVAL_MS, self.health_tick)

    def _health_worker(self):
        for game in list(self.games):
            if game.get("status") == "maintenance":
                continue
            alive = check_health(game)
            self.events.put(("health", game.get("id"), alive))

    def retry_one(self, game):
        self.set_status(f"Comprobando {game.get('title', 'servidor')}…")
        threading.Thread(target=self._retry_worker, args=(game,), daemon=True).start()

    def _retry_worker(self, game):
        self.events.put(("health", game.get("id"), check_health(game)))

    def apply_health(self, game_id, alive):
        if game_id not in self.cards:
            return
        if self.cards[game_id]["game"].get("status") == "maintenance":
            return
        self.states[game_id] = "online" if alive else "offline"
        self._paint(game_id)

    # -- acciones ---------------------------------------------------------
    def play(self, game):
        url = (game.get("url") or "").strip()
        if not url:
            self.show_warning("Este juego no tiene dirección configurada.")
            return
        webbrowser.open(url)
        self.set_status(f"Abriendo {game.get('title')} → {url}")

    def open_studio(self):
        webbrowser.open(STUDIO_URL)
        self.set_status(f"Abriendo Dragon Entertainment Studio → {STUDIO_URL}")

    def _logo_clicked(self):
        play_sound("click")
        self.open_studio()

    def _workarea(self):
        """Área útil de la pantalla, sin los paneles del escritorio."""
        try:
            out = subprocess.run(
                ["xprop", "-root", "_NET_WORKAREA"],
                capture_output=True, text=True, timeout=2,
            ).stdout
            if "=" in out:
                values = [
                    int(n) for n in out.split("=", 1)[1].replace(",", " ").split()
                ]
                if len(values) >= 4:
                    x, y, w, h = values[:4]
                    if w > 400 and h > 300:
                        return x, y, w, h
        except Exception:
            pass
        return 0, 0, self.winfo_screenwidth(), self.winfo_screenheight()

    def _exit_fullscreen(self, _event=None):
        if self._fullscreen:
            self._toggle_fullscreen()

    def _toggle_fullscreen(self):
        play_sound("click")
        try:
            self.attributes("-fullscreen", not self._fullscreen)
            self._fullscreen = not self._fullscreen
        except Exception:
            pass

    def _minimize(self):
        play_sound("click")
        try:
            self.iconify()
        except Exception:
            pass

    def _show_on_top(self):
        """Que la ventana salga por delante al abrir o al volver del icono."""
        try:
            self._minimized = False
            self.deiconify()
            self.lift()
            self.focus_force()
        except Exception:
            pass

    def _on_wake(self, *_args):
        """Otra ejecución del launcher pide que volvamos a mostrarnos."""
        try:
            self.after(0, self._restore_window)
        except Exception:
            pass

    def _restore_window(self):
        self._show_on_top()

    # -- diálogos neón -----------------------------------------------------
    def neon_dialog(self, title, message, buttons, prompt=False, danger=False):
        """Ventana modal con el mismo estilo neón; devuelve el valor elegido."""
        top = tk.Toplevel(self)
        top.withdraw()
        top.overrideredirect(True)
        top.configure(bg=CARD)
        try:
            top.transient(self)
        except Exception:
            pass
        width = 560
        height = 380 if prompt else 300
        x = self.winfo_rootx() + max(0, (self.winfo_width() - width) // 2)
        y = self.winfo_rooty() + max(0, (self.winfo_height() - height) // 2)
        top.geometry(f"{width}x{height}+{x}+{y}")

        canvas = tk.Canvas(top, bg=CARD, highlightthickness=0, bd=0)
        canvas.pack(fill="both", expand=True)
        canvas.create_rectangle(1, 1, width - 1, height - 1, outline=NEON, width=2)
        canvas.create_text(
            width / 2, 44, text=str(title).upper(),
            fill=RED if danger else NEON_HOT,
            font=tkfont.Font(family=FONT, size=13, weight="bold"),
            width=width - 70, justify="center",
        )
        canvas.create_text(
            width / 2, 132 if prompt else 124, text=message, fill=INK_DIM,
            font=tkfont.Font(family=FONT, size=10), width=width - 80,
            justify="center",
        )
        entry = None
        if prompt:
            entry = tk.Entry(
                top, bd=0, relief="flat", highlightthickness=1,
                highlightbackground=NEON_LINE, highlightcolor=NEON,
                bg="#1d0f2e", fg=INK, insertbackground=INK,
                font=(FONT, 10), show="•",
            )
            canvas.create_window(width / 2, 215, window=entry,
                                 width=width - 120, height=32)

        result = {"value": buttons[-1][1]}

        def finish(value):
            if prompt and value:
                value = entry.get().strip()
                if not value:
                    return
            result["value"] = value
            try:
                top.grab_release()
            except Exception:
                pass
            top.destroy()

        count = len(buttons)
        btn_w = int(min(200, (width - 90) / max(1, count)))
        start = width / 2 - (btn_w * count + 10 * (count - 1)) / 2
        for index, (label, value) in enumerate(buttons):
            primary = index == 0 and not danger
            widget = tk.Button(
                top, text=label, command=lambda v=value: finish(v), bd=0,
                relief="flat", highlightthickness=0, font=self.card_btn_font,
                fg="#ffffff" if primary else INK_DIM,
                bg=NEON_DEEP if primary else "#241533",
                activebackground="#9a3bff" if primary else "#33204a",
                activeforeground="#ffffff", cursor="hand2",
            )
            canvas.create_window(
                start + index * (btn_w + 10) + btn_w / 2, height - 40,
                window=widget, width=btn_w, height=38,
            )

        top.bind("<Escape>", lambda _e: finish(buttons[-1][1]))
        top.bind("<Return>", lambda _e: finish(buttons[0][1]))
        top.deiconify()
        top.lift()
        try:
            top.grab_set()
        except Exception:
            pass
        if entry is not None:
            entry.focus_set()
        else:
            top.focus_force()
        self.wait_window(top)
        return result["value"]

    def show_info(self, message):
        self.neon_dialog("Aviso", message, (("ENTENDIDO", True),))

    def show_warning(self, message):
        self.neon_dialog("Atención", message, (("ENTENDIDO", True),))

    def show_error(self, message):
        self.neon_dialog("Error", message, (("ENTENDIDO", True),), danger=True)

    def ask_text(self, title, message):
        value = self.neon_dialog(
            title, message, (("GUARDAR", True), ("CANCELAR", False)),
            prompt=True,
        )
        return value if isinstance(value, str) and value else None

    def _logo_enter(self, _event=None):
        self._logo_hover = True
        self.canvas.configure(cursor="hand2")
        self._draw_logo_glow()

    def _logo_leave(self, _event=None):
        self._logo_hover = False
        self.canvas.configure(cursor="")
        self.canvas.delete("logo-glow")

    def _draw_logo_glow(self):
        """Halo morado neón alrededor del logo al pasar el cursor."""
        self.canvas.delete("logo-glow")
        if (
            self._logo_photo is None
            or getattr(self, "_logo_glow_photo", None) is None
            or self._updating
            or self._confirming
        ):
            return
        logo_h = self._logo_photo.height()
        height = self.canvas.winfo_height() or 680
        x1, y2 = 30.0, height - 12.0
        y1 = y2 - logo_h
        min_x, min_y, max_x, max_y = self._logo_box
        cx = x1 + (min_x + max_x) / 2.0
        cy = y1 + (min_y + max_y) / 2.0
        self.canvas.create_image(
            cx, cy, image=self._logo_glow_photo, tags=("logo-glow",)
        )
        self.canvas.tag_lower("logo-glow", "chrome")
        self.canvas.tag_raise("logo")

    # -- actualizaciones --------------------------------------------------
    def auto_check_updates(self):
        threading.Thread(target=self._update_worker, args=(True,), daemon=True).start()

    def check_updates_clicked(self):
        self.set_status("Buscando actualizaciones del launcher…")
        threading.Thread(target=self._update_worker, args=(False,), daemon=True).start()

    def _update_worker(self, silent):
        try:
            manifest = fetch_manifest()
            latest = manifest.get("version", "0.0.0")
            if parse_version(latest) <= parse_version(VERSION):
                self.events.put(("uptodate", silent))
                return
            self.events.put(("update_available", manifest, silent))
        except Exception as exc:  # noqa: BLE001
            self.events.put(("update_failed", str(exc), silent))

    def ask_update(self, manifest, silent=False):
        if self._updating or self._confirming:
            return
        self._confirming = True
        self._pending_manifest = manifest
        play_sound("click")
        self._draw_confirm_overlay(manifest)

    def _draw_confirm_overlay(self, manifest):
        self._set_chrome_visible(False)
        self._clear_overlay()
        x1, y1, x2, y2, cx = self._overlay_box(320, 620)
        latest = manifest.get("version", "?")
        notes = (manifest.get("notes") or "").strip()
        if len(notes) > 220:
            notes = notes[:217].rstrip() + "…"
        self.canvas.create_text(
            cx, y1 + 38, text="NUEVA ACTUALIZACIÓN DETECTADA", fill=NEON_HOT,
            font=tkfont.Font(family=FONT, size=13, weight="bold"),
            tags=("overlay",),
        )
        self.canvas.create_text(
            cx, y1 + 76, text=f"v{VERSION}   →   v{latest}", fill=INK,
            font=tkfont.Font(family=FONT, size=12), tags=("overlay",),
        )
        self.canvas.create_text(
            cx, y1 + 138, text=notes or "Hay una versión nueva del launcher.",
            fill=INK_DIM, font=tkfont.Font(family=FONT, size=9),
            width=int(x2 - x1 - 90), justify="center", tags=("overlay",),
        )

        yes = tk.Button(
            self.canvas, text="ACTUALIZAR AHORA", command=self._confirm_yes,
            bd=0, relief="flat", highlightthickness=0, font=self.card_btn_font,
            fg="#ffffff", bg=NEON_DEEP, activebackground="#9a3bff",
            activeforeground="#ffffff", cursor="hand2", padx=6, pady=6,
        )
        no = tk.Button(
            self.canvas, text="MÁS TARDE", command=self._confirm_no,
            bd=0, relief="flat", highlightthickness=0, font=self.card_btn_font,
            fg=INK_DIM, bg="#241533", activebackground="#33204a",
            activeforeground="#ffffff", cursor="hand2", padx=6, pady=6,
        )
        self._overlay_widgets = [yes, no]
        btn_w = int(min(230, (x2 - x1) / 2 - 30))
        self.canvas.create_window(
            cx - btn_w / 2 - 8, y2 - 36, window=yes, anchor="center",
            width=btn_w, height=40, tags=("overlay",),
        )
        self.canvas.create_window(
            cx + btn_w / 2 + 8, y2 - 36, window=no, anchor="center",
            width=btn_w, height=40, tags=("overlay",),
        )
        self.set_status(f"Actualización v{latest} disponible")

    def _confirm_yes(self):
        manifest = self._pending_manifest or {}
        self._confirming = False
        self._pending_manifest = None
        play_sound("click")
        self.start_update(manifest)

    def _confirm_no(self):
        self._confirming = False
        self._pending_manifest = None
        self._clear_overlay()
        self._set_chrome_visible(True)
        self._draw_cards()
        self.set_status("Actualización aplazada")

    UPDATE_SECONDS = 10

    def start_update(self, manifest):
        if self._updating:
            return
        self._updating = True
        self._update_manifest = manifest
        self._update_target = None
        self._update_error = None
        self._countdown = self.UPDATE_SECONDS
        play_sound("click")
        self._draw_update_overlay(manifest)
        self.set_status(f"Actualizando a v{manifest.get('version')}…")
        threading.Thread(
            target=self._download_worker, args=(manifest,), daemon=True
        ).start()
        self._countdown_tick()

    def _set_chrome_visible(self, visible):
        state = "normal" if visible else "hidden"
        for item in (getattr(self, "btn_update_win", None),
                     getattr(self, "btn_catalog_win", None)):
            if item:
                try:
                    self.canvas.itemconfigure(item, state=state)
                except Exception:
                    pass

    def _clear_cards(self):
        self.canvas.delete("card")
        for widget in self._card_widgets:
            try:
                widget.destroy()
            except Exception:
                pass
        self._card_widgets = []
        self.cards = {}

    def _clear_overlay(self):
        self.canvas.delete("overlay")
        for widget in self._overlay_widgets:
            try:
                widget.destroy()
            except Exception:
                pass
        self._overlay_widgets = []
        self._count_item = None
        self._progress_item = None

    def _overlay_box(self, box_h, box_w):
        """Fondo oscurecido y panel neón centrado; devuelve sus medidas."""
        width = self.canvas.winfo_width() or 1080
        height = self.canvas.winfo_height() or 680
        self.canvas.delete("card")
        self.canvas.delete("overlay")
        self.canvas.create_rectangle(
            0, 0, width, height, fill="#05020a", outline="",
            stipple="gray75", tags=("overlay",),
        )
        box_w = min(box_w, width - 120)
        x1 = (width - box_w) / 2
        y1 = max(150.0, (height - box_h) / 2)
        x2, y2 = x1 + box_w, y1 + box_h
        self._round_rect(
            x1, y1, x2, y2, 18, fill=CARD, outline=NEON, width=2,
            tags=("overlay",),
        )
        return x1, y1, x2, y2, width / 2

    def _draw_update_overlay(self, manifest):
        self._set_chrome_visible(False)
        self._clear_cards()
        self._clear_overlay()
        x1, y1, x2, y2, cx = self._overlay_box(300, 560)
        latest = manifest.get("version", "?")
        self.canvas.create_text(
            cx, y1 + 34, text="ACTUALIZACIÓN DETECTADA", fill=NEON_HOT,
            font=tkfont.Font(family=FONT, size=12, weight="bold"),
            tags=("overlay",),
        )
        self.canvas.create_text(
            cx, y1 + 66, text=f"v{VERSION}   →   v{latest}", fill=INK,
            font=tkfont.Font(family=FONT, size=11), tags=("overlay",),
        )
        self._count_item = self.canvas.create_text(
            cx, y1 + 146, text=str(self._countdown), fill=NEON,
            font=tkfont.Font(family=FONT, size=46, weight="bold"),
            tags=("overlay",),
        )
        self.canvas.create_text(
            cx, y1 + 196, text="segundos y el launcher se reinicia solo",
            fill=INK_DIM, font=tkfont.Font(family=FONT, size=9),
            tags=("overlay",),
        )
        self._progress_item = self.canvas.create_text(
            cx, y1 + 244, text="Descargando y verificando la firma…",
            fill=INK_FAINT, font=tkfont.Font(family=FONT, size=9),
            tags=("overlay",),
        )

    def _set_overlay(self, item, **options):
        if not item:
            return
        try:
            self.canvas.itemconfigure(item, **options)
        except Exception:
            pass

    def _countdown_tick(self):
        if not self._updating:
            return
        self._set_overlay(
            self._count_item, text=str(max(0, self._countdown))
        )
        if self._countdown > 0:
            self._countdown -= 1
            self.after(1000, self._countdown_tick)
            return
        if self._update_error:
            self._finish_update_error()
            return
        if self._update_target:
            self._restart(self._update_target)
            return
        self._set_overlay(
            self._progress_item, text="Terminando la descarga…", fill=AMBER
        )
        self.after(400, self._countdown_tick)

    def _finish_update_error(self):
        self._updating = False
        self._clear_overlay()
        self._set_chrome_visible(True)
        self._draw_cards()
        self.show_error(f"No se pudo actualizar:\n{self._update_error}")

    def _restart(self, target):
        self._updating = False
        play_sound("close")
        self._fade(1.0, 0.0, 8, 20, on_done=lambda: restart_self(target))

    def _download_worker(self, manifest):
        try:
            target = install_update(manifest)
            self.events.put(("updated", target))
        except Exception as exc:  # noqa: BLE001
            self.events.put(("update_error", str(exc)))

    # -- bucle de eventos -------------------------------------------------
    def _drain_events(self):
        if not self._alive:
            return
        try:
            while True:
                event = self.events.get_nowait()
                kind = event[0]
                if kind == "catalog":
                    self.busy = False
                    self.render(event[1])
                    self.set_status(
                        f"Catálogo actualizado ({len(self.cards)} juegos)"
                    )
                elif kind == "error":
                    self.busy = False
                    self.set_status(event[1])
                    if not self.games:
                        self.show_placeholder(
                            "No hay catálogo.\nComprueba tu conexión y pulsa "
                            "«Buscar estado server»."
                        )
                elif kind == "need_token":
                    self.busy = False
                    self.prompt_token(event[1])
                elif kind == "health":
                    self.apply_health(event[1], event[2])
                elif kind == "update_available":
                    self.ask_update(event[1], event[2])
                elif kind == "uptodate":
                    if not event[1]:
                        self.show_info(f"Ya tienes la última versión (v{VERSION}).")
                    else:
                        self.set_status(f"Launcher actualizado (v{VERSION})")
                elif kind == "update_failed":
                    if not event[2]:
                        self.show_error(
                            f"No se pudo comprobar la actualización:\n{event[1]}"
                        )
                elif kind == "update_error":
                    if self._updating:
                        self._update_error = event[1]
                        self._set_overlay(
                            self._progress_item,
                            text="Error al descargar: se cancela la actualización",
                            fill=RED,
                        )
                    else:
                        self.show_error(f"No se pudo actualizar:\n{event[1]}")
                elif kind == "updated":
                    if self._updating:
                        self._update_target = event[1]
                        self._set_overlay(
                            self._progress_item,
                            text="Descarga verificada. Reiniciando…",
                            fill=GREEN,
                        )
                    else:
                        self.set_status("Actualizado. Reiniciando…")
                        self.after(400, lambda: restart_self(event[1]))
        except queue.Empty:
            pass
        if self._alive:
            self.after(200, self._drain_events)


# --------------------------------------------------------------------------
# Actualización firmada (formato UpdateKit)
# --------------------------------------------------------------------------
def fetch_manifest():
    raw = json.loads(
        fetch_repo_file("updates/stable/manifest.json", timeout=12).decode("utf-8")
    )
    signed = raw.get("signed")
    signature = raw.get("signature")
    if not isinstance(signed, dict) or not isinstance(signature, str):
        raise ValueError("manifiesto sin firma")
    import base64

    public_key = pem_to_raw_public_key(PUBLIC_PEM)
    message = canonical_json(signed).encode("utf-8")
    if not ed25519_verify(public_key, base64.b64decode(signature), message):
        raise ValueError("firma del manifiesto inválida: actualización rechazada")
    if signed.get("appId") != APP_ID:
        raise ValueError(f"el manifiesto es de otra app ({signed.get('appId')})")
    if signed.get("channel") != CHANNEL:
        raise ValueError(f"canal inesperado ({signed.get('channel')})")
    return signed


def _pick_asset(manifest):
    assets = manifest.get("assets") or []
    wanted = BINARY_ASSET if FROZEN else SCRIPT_ASSET
    for asset in assets:
        if asset.get("fileName") == wanted:
            return asset
    if FROZEN:
        raise ValueError("esta versión no trae el ejecutable para Linux")
    for asset in assets:
        if asset.get("platform") in ("linux", "any") and asset.get("arch") in (
            "x64", "x86_64", "amd64", "any",
        ):
            return asset
    for asset in assets:
        if asset.get("platform") in ("linux", "any"):
            return asset
    raise ValueError("el manifiesto no trae un archivo para Linux")


def install_update(manifest):
    asset = _pick_asset(manifest)
    # El ejecutable de un solo archivo pesa decenas de MB: el límite de
    # descarga se ajusta a lo que diga el manifiesto.
    expected = int(asset.get("size") or 0)
    limit = max(8 * 1024 * 1024, expected + 2 * 1024 * 1024)
    timeout = 300 if FROZEN else 30
    try:
        data = http_get(asset["url"], timeout=timeout, max_bytes=limit)
    except urllib.error.HTTPError as exc:
        if exc.code not in (401, 403, 404):
            raise
        data = fetch_repo_file(
            "launcher/" + (asset.get("fileName") or "fp_launcher.py"),
            timeout=timeout, max_bytes=limit,
        )
    digest = hashlib.sha256(data).hexdigest()
    if asset.get("sha256") and digest.lower() != str(asset["sha256"]).lower():
        raise ValueError("el SHA-256 no coincide con el manifiesto")
    if asset.get("size") and int(asset["size"]) != len(data):
        raise ValueError("el tamaño no coincide con el manifiesto")
    target = os.path.abspath(sys.executable if FROZEN else __file__)
    directory = os.path.dirname(target) or "."
    fd, temp_path = tempfile.mkstemp(prefix=".fp_launcher_", dir=directory)
    with os.fdopen(fd, "wb") as fh:
        fh.write(data)
    os.chmod(temp_path, 0o755)
    if not FROZEN:
        backup = target + ".bak"
        try:
            shutil.copy2(target, backup)
        except Exception:
            pass
    # Reemplazar el archivo en uso funciona en Linux (se renombra encima).
    os.replace(temp_path, target)
    return target


def restart_self(target):
    if FROZEN:
        os.execv(sys.executable, [sys.executable, "--restarted"])
    os.execv(sys.executable, [sys.executable, target, "--restarted"])


# --------------------------------------------------------------------------
# Autoprueba (la usa el panel antes de publicar)
# --------------------------------------------------------------------------
def self_test():
    import base64

    vectors = [
        (
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
            "",
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155"
            "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
        ),
        (
            "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
            "72",
            "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da"
            "085ac1e43e15996e458f3613d0f11d8c387b2eaeb4302aeeb00d291612bb0c00",
        ),
    ]
    for public_hex, message_hex, signature_hex in vectors:
        ok = ed25519_verify(
            bytes.fromhex(public_hex),
            bytes.fromhex(signature_hex),
            bytes.fromhex(message_hex),
        )
        if not ok:
            print("FALLO: vector Ed25519 no válido")
            return 1
    # El canonical_json debe coincidir con el del UpdateKit.
    sample = {"b": [1, 2, {"z": None, "a": True}], "a": "ñ"}
    expected = '{"a":"ñ","b":[1,2,{"a":true,"z":null}]}'
    if canonical_json(sample) != expected:
        print(f"FALLO canonical_json: {canonical_json(sample)}")
        return 1
    if hex_mix("#000000", "#ffffff", 0.5) != "#808080":
        print("FALLO hex_mix")
        return 1
    if len(_synth("click")) < 1000 or len(_synth("open")) < 10000:
        print("FALLO: síntesis de sonido")
        return 1
    if struct.pack("<3h", -32768, 0, 32767) != b"\x00\x80\x00\x00\xff\x7f":
        print("FALLO: empaquetado de audio")
        return 1
    pem_to_raw_public_key(PUBLIC_PEM)
    base64.b64decode("AAAA")
    print("Autoprueba OK")
    return 0


def _instance_path():
    return os.path.join(CONFIG_DIR, "instance.pid")


def claim_single_instance():
    """Si ya hay un launcher abierto, lo restaura en vez de abrir otro."""
    path = _instance_path()
    try:
        with open(path, "r", encoding="utf-8") as fh:
            pid = int(fh.read().strip() or 0)
    except Exception:
        pid = 0
    if pid and pid != os.getpid():
        try:
            with open(f"/proc/{pid}/cmdline", "rb") as fh:
                cmdline = fh.read().decode("utf-8", "replace")
        except Exception:
            cmdline = ""
        if "fp_launcher" in cmdline.replace("-", "_"):
            try:
                os.kill(pid, signal.SIGUSR1)
                return False
            except Exception:
                pass
    try:
        os.makedirs(CONFIG_DIR, exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(str(os.getpid()))
    except Exception:
        pass
    return True


def release_instance():
    try:
        path = _instance_path()
        with open(path, "r", encoding="utf-8") as fh:
            if int(fh.read().strip() or 0) != os.getpid():
                return
        os.remove(path)
    except Exception:
        pass


def main():
    if "--self-test" in sys.argv:
        return self_test()
    if not claim_single_instance():
        return 0
    app = Launcher()
    app.mainloop()
    release_instance()
    return 0


if __name__ == "__main__":
    sys.exit(main())
