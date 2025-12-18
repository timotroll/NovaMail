# -*- coding: utf-8 -*-
"""
NovaMail — natasha + multiacc + DPI + sticky-footer + sources-pool (NO GLOBAL SOURCE)
- Natasha для извлечения имени/отчества
- Шаблоны с/без {fio}
- Антидубль sent_emails.txt
- Вложения
- Рандомные лимиты и задержки
- Расписание по дням недели (в одну строку) + случайный дрейф ±N минут
- МУЛЬТИАККАУНТЫ SMTP (только они)
- Тестовая отправка — со всех аккаунтов на один e-mail (НЕ блокирует UI)
- Авто-DPI; центральная область прокручиваемая; нижняя панель с кнопками всегда видима
- Колесо мыши: при наведении на текстовые поля прокручивается только их содержимое
- Пул источников: несколько файлов с ID; привязка аккаунта к файлу через src=ID (или 7-е поле)
  Для каждого файла — свои колонки/строка старта.
- Глобальный источник ОТКЛЮЧЕН: отправка только если у аккаунта есть валидный src=ID.

Запуск: python novamail_bot.py
"""

import os
import re
import json
import time
import queue
import smtplib
import threading
import random
import mimetypes
import sqlite3
import urllib.request
import urllib.error
import html
import webbrowser
import tempfile
from datetime import datetime, timedelta
from email.message import EmailMessage
from pathlib import Path
from typing import List, Optional, Tuple, Set, Dict, Any
from smtplib import SMTPServerDisconnected
from dataclasses import dataclass

# --- Гарантируем доступ к словарям pymorphy2 (важно для EXE) ---
import pymorphy2_dicts_ru as pmru
os.environ["PYMORPHY2_DICT_PATH"] = pmru.get_path()

import pandas as pd
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog

# === ОБЯЗАТЕЛЬНО: Natasha ===
from natasha import NamesExtractor, MorphVocab

try:
    from tkhtmlview import HTMLLabel  # type: ignore
except Exception:
    HTMLLabel = None

APP_NAME = "NovaMail"
CONFIG_FILE = Path(__file__).with_suffix(".json")

# антидубль
SENT_LIST_FILE = Path(__file__).with_name("sent_emails.txt")
SENT_DB_FILE = Path(__file__).with_name("sent_mail_log.sqlite3")
LLM_TEMPLATE_FILE = Path(__file__).with_name("template_llm_email.html")

OLLAMA_URL = os.environ.get("OLLAMA_URL", "http://localhost:11434")
OLLAMA_MODEL = os.environ.get("OLLAMA_MODEL", "email-writer")
LLM_PLACEHOLDERS = [
    "preheader",
    "brand_name",
    "brand_tagline",
    "email_date",
    "headline1",
    "headline2",
    "intro_text",
    "updates_title",
    "updates_item_1",
    "updates_item_2",
    "updates_item_3",
]

UI_APP_BG = "#050b1a"
UI_SURFACE_BG = "#0b162d"
UI_CARD_BG = "#111f3f"
UI_ACCENT = "#5c7cfa"
UI_ACCENT_HOVER = "#4c6ef5"
UI_DANGER = "#ef4444"
UI_DANGER_HOVER = "#dc2626"
UI_TEXT = "#f8fafc"
UI_TEXT_MUTED = "#cdd6f7"
UI_BORDER = "#1f2d4a"
UI_BTN = "#1a2644"
UI_BTN_HOVER = "#233152"
UI_BTN_ACTIVE = "#121c31"

# SMTP keepalive
KEEPALIVE_STEP_SEC = 25

# ==========================
# Natasha
# ==========================
_morph_vocab = MorphVocab()
_names_extractor = NamesExtractor(_morph_vocab)

# ==========================
# Справочники/регэкспы
# ==========================
EMAIL_REGEX = re.compile(r"[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}")
PHONE_REGEX = re.compile(r"\+?\d[\d\-\s\(\)]{6,}\d")
ONLY_LETTERS_REGEX = re.compile(r"[^A-Za-zА-Яа-яЁё\.\-\s]")

STOPWORDS_NEAR = {
    "не", "работает", "вакансия", "удалён", "удален", "уволен", "нет", "замена",
    "бывш", "временно"
}

RUS_FIRST_NAMES = {
    "агафья","агата","агнесса","ада","аделина","аделя","адиля","алевтина","александра","алесса","алиса","алла",
    "алёна","алена","алина","амина","анастасия","ангелина","анжелика","анжела","анна","антонина","анфиса",
    "арина","белла","валентина","валерия","варвара","василиса","вера","вероника","виктория","галина","дарина","дарья",
    "дина","диана","ева","евгения","екатерина","елена","елизавета","жана","жанна","зарина","зинаида","злата","зоя",
    "илона","инна","ирина","карина","каролина","катерина","кира","кристина","ксения","лада","лариса","лиана",
    "лидия","лилия","лилиана","лиза","луиза","люба","любовь","людмила","мадина","майя","маргарита","марина","мария",
    "мирослава","мила","милана","наталия","наталья","надежда","ника","нина","оксана","олеся","оливия","ольга","полина",
    "раиса","регина","рената","рита","сабина","светлана","снежана","соня","софия","софья","таисия","тамара","татьяна",
    "ульяна","фаина","эмилия","эмма","юлиана","юлия","яна","ярослава",
    "аарон","абрам","агафон","адам","адриан","азар","азарий","айдар","айрат","акакий","александр","алексей","альберт",
    "анатолий","андрей","антон","аркадий","арсений","артем","артём","артемий","артур","богдан","борис","вадим","валентин",
    "валерий","василий","вениамин","виктор","виталий","влад","владимир","владислав","вячеслав","геннадий","георгий",
    "герман","глеб","григорий","даниил","данила","денис","дмитрий","евгений","егор","иван","игорь","илья","карен",
    "кирилл","константин","лев","леонид","макар","максим","марат","марк","матвей","михаил","мирон","никита","николай",
    "олег","павел","петр","пётр","платон","родион","роман","руслан","савва","савелий","семен","семён","сергей",
    "степан","терентий","тимофей","тимур","тихон","федор","фёдор","филипп","харитон","эдуард","юрий","яков","ярослав"
}

COMMON_RU_NAMES = {
    "алексей","александр","андрей","анна","антон","арина","арсений","артем","артём","артемий","борис","богдан",
    "вадим","валерий","валентина","валерия","варвара","василий","вера","вероника","виктор","виктория",
    "виталий","владимир","владислав","вячеслав","галина","георгий","герман","глеб","григорий","дарья","денис",
    "диана","дмитрий","евгений","егор","екатерина","елена","елизавета","иван","игорь","илья","кирилл",
    "константин","ксения","лев","леонид","лилия","любовь","людмила","максим","маргарита","марина","марк","мария",
    "матвей","михаил","наталья","никита","николай","олег","олеся","ольга","оксана","павел","пётр","полина","роман",
    "руслан","савелий","семён","сергей","светлана","степан","таисия","тамара","татьяна","тимофей","тимур","ульяна",
    "фёдор","юлия","юрий","яков","яна","ярослав","софья","софия","кристина","карина"
}

WORD_FLEX = r"(?:[А-ЯЁA-Z][а-яёa-z]+(?:-[А-ЯЁA-Z][а-яёa-z]+)?|[А-ЯЁA-Z]{2,}(?:-[А-ЯЁA-Z]{2,})?)"
PAT_IO   = re.compile(rf"\b({WORD_FLEX})\s+({WORD_FLEX})\b")
PAT_FIO  = re.compile(rf"\b({WORD_FLEX})\s+({WORD_FLEX})\s+({WORD_FLEX})\b")
PAT_SINGLE = re.compile(rf"\b({WORD_FLEX})\b")

PATRONYMIC_SUFFIXES = [
    "овна", "евна", "ёвна", "ьевна", "ична", "инична",
    "ович", "евич", "ёвич", "ьевич", "ич",
]
PATRONYMIC_RE = re.compile(r"(?:%s)$" % "|".join(map(re.escape, PATRONYMIC_SUFFIXES)), re.IGNORECASE)

# ==========================
# Утилиты текста/FIO
# ==========================
def _smart_title(token: str) -> str:
    if re.fullmatch(r"[А-ЯЁA-Z]\.[А-ЯЁA-Z]\.", token):
        return token
    parts = token.split("-")
    t = []
    for p in parts:
        if p.isupper():
            p = p.title()
        else:
            p = p[:1].upper() + p[1:].lower()
        t.append(p)
    return "-".join(t)

def _clean_text(text: str) -> str:
    text = EMAIL_REGEX.sub(" ", text)
    text = PHONE_REGEX.sub(" ", text)
    text = ONLY_LETTERS_REGEX.sub(" ", text)
    return re.sub(r"\s+", " ", text).strip()

def _contains_stop_context(around: str) -> bool:
    tokens = set(_clean_text(around.lower()).split())
    return any(sw in tokens for sw in STOPWORDS_NEAR)

def _score_candidate(name: str, context: str) -> float:
    score = 1.0
    parts = name.split()
    if parts and parts[0].lower() in COMMON_RU_NAMES:
        score += 1.0
    if name.isupper():
        score += 0.3
    if _contains_stop_context(context):
        score -= 1.0
    return score

def _norm(s: str) -> str:
    return s.lower().replace("ё", "е")

def _lev(a: str, b: str) -> int:
    a, b = _norm(a), _norm(b)
    m, n = len(a), len(b)
    dp = list(range(n + 1))
    for i in range(1, m + 1):
        prev, dp[0] = dp[0], i
        for j in range(1, n + 1):
            cur = dp[j]
            cost = 0 if a[i - 1] == b[j - 1] else 1
            dp[j] = min(dp[j] + 1, dp[j - 1] + 1, prev + cost)
            prev = cur
    return dp[n]

def _first_name_is_valid(name: str) -> bool:
    n = _norm(name)
    if n in RUS_FIRST_NAMES:
        return True
    best = min((_lev(n, v) for v in RUS_FIRST_NAMES), default=99)
    return best <= 1

def extract_emails(text) -> List[str]:
    if not isinstance(text, str):
        text = "" if pd.isna(text) else str(text)
    text = text.replace(",", " ").replace(";", " ").replace("\n", " ")
    found = EMAIL_REGEX.findall(text)
    unique: List[str] = []
    for e in found:
        e = e.strip().lower()
        if e and e not in unique:
            unique.append(e)
    return unique

def _accept_candidate(cand: str) -> Optional[str]:
    parts = cand.split()
    if not parts:
        return None
    first = parts[0]
    if not _first_name_is_valid(first):
        return None
    return " ".join(_smart_title(w) for w in parts)

def extract_fio(raw) -> str:
    if pd.isna(raw):
        return ""
    text = str(raw).replace('"', " ").replace("«", " ").replace("»", " ").replace("\n", " ")

    def norm_and_score(cand: str, base: float) -> Tuple[str, float]:
        cand_norm = _accept_candidate(cand)
        if not cand_norm:
            return "", -1e9
        parts = cand_norm.split()
        score = base + _score_candidate(cand_norm, text)
        if len(parts) == 2 and PATRONYMIC_RE.search(parts[1]):
            score += 0.8
        if len(parts) == 2:
            score += 0.6
        return cand_norm, score

    best: Tuple[str, float] = ("", -1.0)

    for match in _names_extractor(text):
        first = (match.fact.first or "").strip()
        middle = (match.fact.middle or "").strip()
        if first and middle:
            cand, score = norm_and_score(f"{first} {middle}", base=1.8)
            if score > best[1]:
                best = (cand, score)
        elif first:
            cand, score = norm_and_score(first, base=0.7)
            if score > best[1]:
                best = (cand, score)

    for m in PAT_FIO.finditer(text):
        name, pat = m.group(2), m.group(3)
        if re.fullmatch(r"[А-ЯЁA-Z]\.", name) or re.fullmatch(r"[А-ЯЁA-Z]\.", pat):
            continue
        cand, score = norm_and_score(f"{name} {pat}", base=1.6)
        if score > best[1]:
            best = (cand, score)

    m = PAT_IO.search(text)
    if m:
        cand, score = norm_and_score(f"{m.group(1)} {m.group(2)}", base=1.4)
        if score > best[1]:
            best = (cand, score)

    if best[0] == "":
        for m in PAT_SINGLE.finditer(text):
            word = _smart_title(m.group(1))
            if _first_name_is_valid(word):
                cand, score = norm_and_score(word, base=0.6)
                if score > best[1]:
                    best = (cand, score)

    if best[0]:
        return best[0]

    cleaned = _clean_text(text)
    parts = cleaned.split()
    if len(parts) >= 2:
        a, b = parts[0], parts[1]
        if (re.fullmatch(r"[А-ЯЁA-Z]{2,}", a) or re.fullmatch(r"[А-ЯЁA-Z][а-яёa-z]+", a)) and \
           (re.fullmatch(r"[А-ЯЁA-Z]{2,}", b) or re.fullmatch(r"[А-ЯЁA-Z][а-яёa-z]+", b)):
            return " ".join((_smart_title(a), _smart_title(b)))
    return ""

# ==========================
# Чтение таблицы
# ==========================
def read_table(path: str, start_row: int = 2) -> pd.DataFrame:
    path_obj = Path(path)
    if not path_obj.exists():
        raise FileNotFoundError(f"Файл не найден: {path}")
    if path_obj.suffix.lower() in (".xlsx", ".xlsm", ".xls"):
        df = pd.read_excel(path, header=None, engine="openpyxl")
    elif path_obj.suffix.lower() == ".csv":
        df = pd.read_csv(path, header=None, sep=None, engine="python")
    else:
        raise ValueError("Поддерживаются только файлы .xlsx/.xls/.csv")
    if start_row > 1:
        df = df.iloc[start_row-1:, :].reset_index(drop=True)
    return df

# ==========================
# SMTP
# ==========================
class SMTPSender:
    def __init__(self, host: str, port: int, security: str, login: str, password: str, from_name: str = ""):
        self.host = host
        self.port = port
        self.security = security  # "SSL" | "STARTTLS" | "PLAIN"
        self.login = login
        self.password = password
        self.from_name = from_name.strip()
        self.server = None

    def connect(self):
        if self.security == "SSL":
            srv = smtplib.SMTP_SSL(self.host, self.port, timeout=60)
            if self.login:
                srv.login(self.login, self.password)
        else:
            srv = smtplib.SMTP(self.host, self.port, timeout=60)
            srv.ehlo()
            if self.security == "STARTTLS":
                srv.starttls()
                srv.ehlo()
            if self.login:
                srv.login(self.login, self.password)
        self.server = srv

    def close(self):
        try:
            if self.server:
                try:
                    self.server.quit()
                except Exception:
                    self.server.close()
        finally:
            self.server = None

    def ping(self) -> bool:
        if not self.server:
            return False
        try:
            self.server.noop()
            return True
        except Exception:
            return False

    def ensure_connected(self):
        if not self.ping():
            self.close()
            self.connect()

    def send(self, to_email: str, subject: str, body: str,
             attachments: Optional[List[str]] = None,
             body_html: Optional[str] = None) -> None:
        if not self.server:
            raise RuntimeError("SMTP не подключен")

        msg = EmailMessage()
        sender = f"{self.from_name} <{self.login}>" if self.from_name else self.login
        msg["From"] = sender
        msg["To"] = to_email
        msg["Subject"] = subject

        if body_html:
            plain = body if body else re.sub(r"<[^>]+>", " ", body_html)
            msg.set_content(plain, subtype="plain", charset="utf-8")
            msg.add_alternative(body_html, subtype="html", charset="utf-8")
        else:
            msg.set_content(body, subtype="plain", charset="utf-8")

        if attachments:
            for path in attachments:
                with open(path, "rb") as f:
                    data = f.read()
                ctype, _ = mimetypes.guess_type(path)
                if ctype is None:
                    ctype = "application/octet-stream"
                maintype, subtype = ctype.split("/", 1)
                msg.add_attachment(data, maintype=maintype, subtype=subtype,
                                   filename=os.path.basename(path))

        tried_reconnect = False
        while True:
            try:
                self.server.send_message(msg)
                return
            except (SMTPServerDisconnected, OSError):
                if tried_reconnect:
                    raise
                tried_reconnect = True
                self.close()
                self.connect()
            except Exception:
                if tried_reconnect:
                    raise
                tried_reconnect = True
                self.close()
                self.connect()

# --- Модель SMTP-аккаунта ---
@dataclass
class SMTPAccount:
    host: str
    port: int
    security: str  # "SSL" | "STARTTLS" | "PLAIN"
    login: str
    password: str
    from_name: str = ""
    src_id: Optional[int] = None  # <-- ID источника из пула

# ==========================
# Прокручиваемый фрейм
# ==========================
class ScrollableFrame(ttk.Frame):
    def __init__(self, parent, *args, **kwargs):
        kwargs.setdefault("style", "Content.TFrame")
        super().__init__(parent, *args, **kwargs)
        self.canvas = tk.Canvas(self, borderwidth=0, highlightthickness=0,
                                background=UI_SURFACE_BG)
        self.vsb = ttk.Scrollbar(self, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set, background=UI_SURFACE_BG)

        self.inner = ttk.Frame(self.canvas, style="Content.TFrame")
        self.inner_id = self.canvas.create_window((0, 0), window=self.inner, anchor="nw")

        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.vsb.grid(row=0, column=1, sticky="ns")
        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=1)

        self.inner.bind("<Configure>", self._on_inner_configure)
        self.canvas.bind("<Configure>", self._on_canvas_configure)

        # ПРОКРУТКА
        self.canvas.bind("<MouseWheel>", self._on_mousewheel)
        self.inner.bind("<MouseWheel>", self._on_mousewheel)
        self.canvas.bind("<Button-4>", self._on_mousewheel)
        self.canvas.bind("<Button-5>", self._on_mousewheel)
        self.inner.bind("<Button-4>", self._on_mousewheel)
        self.inner.bind("<Button-5>", self._on_mousewheel)

    def _on_inner_configure(self, event):
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        self.canvas.itemconfig(self.inner_id, width=self.canvas.winfo_width())

    def _on_canvas_configure(self, event):
        self.canvas.itemconfig(self.inner_id, width=event.width)

    def _on_mousewheel(self, event):
        wclass = event.widget.winfo_class()
        if wclass in ("Text", "Entry", "TEntry", "Listbox"):
            return "break"
        delta = 0
        if getattr(event, "num", None) in (4, 5):
            delta = -1 if event.num == 4 else 1
        elif getattr(event, "delta", 0) != 0:
            delta = -1 if event.delta > 0 else 1
        if delta != 0:
            self.canvas.yview_scroll(delta, "units")
            return "break"

# ==========================
# GUI
# ==========================
class App(tk.Tk):
    def __init__(self):
        # DPI/масштаб — до создания виджетов
        self._init_dpi_awareness()
        super().__init__()
        self.title(APP_NAME)

        # очередь/треды
        self.queue = queue.Queue()
        self.stop_event = threading.Event()

        # Планировщик
        self.scheduler_thread: Optional[threading.Thread] = None
        self.scheduler_stop_event = threading.Event()
        self.last_run_date: Optional[str] = None  # 'YYYY-MM-DD'

        # Статус
        self.status_var = tk.StringVar(value="Готово")

        # Геометрия
        self._apply_dynamic_geometry()
        self._init_styles()

        # Мультиаккаунты (только они)
        self.smtp_accounts_text = tk.StringVar(value=
            "user1@example.com;app-password-1;smtp.gmail.com;465;SSL;Менеджер 1;src=1\n"
            "user2@example.com;app-password-2;smtp.gmail.com;465;SSL;Менеджер 2;src=2"
        )
        self.sending_threads_multi: List[threading.Thread] = []
        self.sending_thread_single: Optional[threading.Thread] = None

        # Значения по умолчанию для добавляемых источников (используются в менеджере)
        self.def_start_row = tk.IntVar(value=2)
        self.def_email_col = tk.IntVar(value=9)
        self.def_fio_from = tk.IntVar(value=27)
        self.def_fio_to = tk.IntVar(value=34)

        # Пул источников
        self.sources_pool: List[Dict[str, Any]] = []
        # Поведение — лимит/задержки
        self.limit_count = tk.IntVar(value=30)
        self.delay_sec = tk.IntVar(value=60)
        self.pair_mode = tk.BooleanVar(value=False)

        # Рандомные лимиты/задержки
        self.random_limit_enabled = tk.BooleanVar(value=False)
        self.limit_min = tk.IntVar(value=30)
        self.limit_max = tk.IntVar(value=40)
        self.random_delay_enabled = tk.BooleanVar(value=False)
        self.delay_min = tk.IntVar(value=15)
        self.delay_max = tk.IntVar(value=80)

        # Расписание
        self.schedule_enabled = tk.BooleanVar(value=False)
        self.schedule_days_vars = {
            0: tk.BooleanVar(value=True),
            1: tk.BooleanVar(value=True),
            2: tk.BooleanVar(value=True),
            3: tk.BooleanVar(value=True),
            4: tk.BooleanVar(value=True),
            5: tk.BooleanVar(value=False),
            6: tk.BooleanVar(value=False),
        }
        self.schedule_times = {
            0: tk.StringVar(value="10:30"),
            1: tk.StringVar(value="10:30"),
            2: tk.StringVar(value="10:30"),
            3: tk.StringVar(value="10:30"),
            4: tk.StringVar(value="10:30"),
            5: tk.StringVar(value="00:00"),
            6: tk.StringVar(value="00:00"),
        }
        self.rand_time_enabled = tk.BooleanVar(value=True)
        self.rand_time_min = tk.IntVar(value=10)
        self.rand_time_max = tk.IntVar(value=90)

        # Шаблоны
        self.subject_tpl = tk.StringVar(value="От НОВАМЕБЕЛЬ {fio}")
        self.body_tpl = tk.StringVar(value="Здравствуйте, {fio}!\n\nТестовое сообщение.\n\nС уважением,\nВаша компания.")
        self.subject_tpl_nofio = tk.StringVar(value="От НОВАМЕБЕЛЬ")
        self.body_tpl_nofio = tk.StringVar(value="Здравствуйте!\n\nТестовое сообщение.\n\nС уважением,\nВаша компания.")
        self.mailing_id = tk.StringVar(value="")
        self.active_mailing_id = ""
        self.campaign_theme = tk.StringVar(value="")
        self._campaign_wishes_value = ""
        self.active_subject_tpl = ""
        self.preview_target_email = tk.StringVar(value="demo@example.com")
        self.preview_fio = "Марина Иванова"
        self.preview_last_html: Optional[str] = None
        self.html_render_available = False
        self.attachments_description = tk.StringVar(value="")
        self.company_site = tk.StringVar(value="https://example.com")

        # Вложения
        self.attachments: List[str] = []
        self.active_attachments_description = ""

        # Антидубль
        self.sent_list_file = SENT_LIST_FILE
        self.sent_lock = threading.Lock()
        self.sent_emails: Set[str] = set()
        self._load_sent_emails()
        self.sent_db_path = SENT_DB_FILE
        self.sent_db_lock = threading.Lock()
        self._init_sent_db()
        self._init_app_db()
        self.llm_template = self._load_llm_template()
        self.active_campaign_theme = ""
        self.active_campaign_wishes = ""

        # === Каркас макета ===
        self._build_menu()
        self._build_layout_shell()
        self._build_scrollable_content()
        self._set_schedule_controls_state()
        self._install_clipboard_features()
        self._restyle_all_buttons()
        self._wire_schedule_toggle()

        # Конфиг
        self.load_config()
        self._refresh_db_summaries()

        # Лог-дренаж
        self.after(120, self._drain_queue)

        self.status_var.set(f"Готово | антидубль: {len(self.sent_emails)} e-mail")

    # --- DPI / масштаб ---
    def _init_dpi_awareness(self):
        try:
            import ctypes
            try:
                ctypes.windll.shcore.SetProcessDpiAwareness(2)
            except Exception:
                try:
                    ctypes.windll.user32.SetProcessDPIAware()
                except Exception:
                    pass
        except Exception:
            pass
        try:
            _tmp = tk.Tk(); _tmp.withdraw()
            px = _tmp.winfo_fpixels('1i')
            scale = max(0.9, min(1.8, px / 96.0))
            _tmp.tk.call('tk', 'scaling', scale)
            _tmp.destroy()
        except Exception:
            pass

    def _apply_dynamic_geometry(self):
        base_w, base_h = 1380, 900
        try:
            self.geometry(f"{base_w}x{base_h}+50+40")
            self.minsize(960, 640)
        except Exception:
            pass

    def _init_styles(self):
        self.configure(bg=UI_APP_BG)
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("TFrame", background=UI_SURFACE_BG)
        style.configure("Content.TFrame", background=UI_SURFACE_BG)
        style.configure("Card.TFrame", background=UI_CARD_BG)
        style.configure("TLabel", background=UI_CARD_BG, foreground=UI_TEXT)
        style.configure("TCheckbutton", background=UI_CARD_BG, foreground=UI_TEXT)
        style.configure("TRadiobutton", background=UI_CARD_BG, foreground=UI_TEXT)
        style.configure("Card.TLabelframe", background=UI_CARD_BG, foreground=UI_TEXT_MUTED, borderwidth=0)
        style.configure("Card.TLabelframe.Label", background=UI_CARD_BG, foreground=UI_TEXT)
        style.configure("Footer.TFrame", background=UI_SURFACE_BG)
        style.configure("Status.TLabel", background=UI_BORDER, foreground=UI_TEXT, padding=6)
        style.configure("Treeview", background=UI_CARD_BG, fieldbackground=UI_CARD_BG,
                        foreground=UI_TEXT, bordercolor=UI_BORDER, rowheight=24)
        style.configure("Treeview.Heading", background=UI_SURFACE_BG, foreground=UI_TEXT,
                        font=("Segoe UI", 10, "bold"))
        style.map("Treeview", background=[("selected", UI_ACCENT)], foreground=[("selected", "#ffffff")])

        base_btn_opts = dict(
            padding=(14, 10),
            relief="flat",
            borderwidth=0,
            focusthickness=0,
            anchor="center",
            font=("Segoe UI", 10, "bold"),
        )
        style.configure("TButton",
                        background=UI_BTN,
                        foreground=UI_TEXT,
                        **base_btn_opts)
        style.map("TButton",
                  background=[("active", UI_BTN_HOVER), ("pressed", UI_BTN_ACTIVE), ("disabled", "#2f3b59")],
                  relief=[("pressed", "flat"), ("!pressed", "flat")])

        style.configure("Accent.TButton",
                        background=UI_ACCENT,
                        foreground="#ffffff",
                        **base_btn_opts)
        style.map("Accent.TButton",
                  background=[("active", UI_ACCENT_HOVER), ("pressed", "#3b5bdb"), ("disabled", "#4b5563")],
                  relief=[("pressed", "flat"), ("!pressed", "flat")])

        style.configure("Danger.TButton",
                        background=UI_DANGER,
                        foreground="#ffffff",
                        **base_btn_opts)
        style.map("Danger.TButton",
                  background=[("active", UI_DANGER_HOVER), ("pressed", "#b91c1c"), ("disabled", "#4b5563")],
                  relief=[("pressed", "flat"), ("!pressed", "flat")])

        style.configure("HeroTitle.TLabel", background=UI_APP_BG, foreground=UI_TEXT,
                        font=("Segoe UI", 20, "bold"))
        style.configure("HeroCaption.TLabel", background=UI_APP_BG, foreground=UI_TEXT_MUTED,
                        font=("Segoe UI", 11))
        style.configure("StatusValue.TLabel", background=UI_BORDER, foreground=UI_TEXT,
                        font=("Segoe UI", 9))
        style.configure("Card.TSeparator", background=UI_BORDER)

    # --- Меню/хоткеи ---
    def _build_menu(self):
        menubar = tk.Menu(self)

        filemenu = tk.Menu(menubar, tearoff=0)
        filemenu.add_command(label="Сохранить настройки", command=self.save_config)
        filemenu.add_command(label="Загрузить настройки", command=self.load_config)
        filemenu.add_separator()
        filemenu.add_command(label="Очистить список отправленных e-mail", command=self.clear_sent_emails)
        filemenu.add_separator()
        filemenu.add_command(label="Выход", command=self.on_close)
        menubar.add_cascade(label="Файл", menu=filemenu)

        self.config(menu=menubar)

    # --- Каркас: верх/центр/низ ---
    def _build_layout_shell(self):
        hero = tk.Frame(self, bg=UI_APP_BG)
        hero.pack(side="top", fill="x")
        ttk.Label(hero, text="NovaMail", style="HeroTitle.TLabel").pack(anchor="w", padx=26, pady=(18, 4))
        ttk.Label(hero,
                  text="NovaMail — мульти-SMTP рассылки с LLM, антидублем, источниками и расписанием.",
                  style="HeroCaption.TLabel").pack(anchor="w", padx=26)
        tk.Label(hero, text="AI EDITION", bg=UI_ACCENT, fg="#ffffff",
                 font=("Segoe UI", 10, "bold"), padx=12, pady=4,
                 bd=0, highlightthickness=0).pack(anchor="w", padx=26, pady=(6, 16))

        self.status_bar = ttk.Label(self, textvariable=self.status_var, anchor="w", style="Status.TLabel")
        self.status_bar.pack(side="top", fill="x")

        self.scroll_host = ScrollableFrame(self)
        self.scroll_host.pack(side="top", fill="both", expand=True)

        self.footer = ttk.Frame(self, padding=(14, 12), style="Footer.TFrame")
        self.footer.pack(side="bottom", fill="x")
        self.btn_clear_sent = ttk.Button(self.footer, text="Очистить антидубль", command=self.clear_sent_emails)
        self.btn_clear_sent.pack(side="right", padx=(4,0))
        self.btn_stop = ttk.Button(self.footer, text="Стоп", command=self.stop_sending, style="Danger.TButton")
        self.btn_stop.pack(side="right", padx=6)
        self.btn_start = ttk.Button(self.footer, text="Старт", command=self.start_sending, style="Accent.TButton")
        self.btn_start.pack(side="right", padx=(0,6))
        self._set_buttons_state(False)

        # --- Внутреннее содержимое ---
    def _build_scrollable_content(self):
        root = self.scroll_host.inner
        root.grid_columnconfigure(0, weight=3)
        root.grid_columnconfigure(1, weight=4, minsize=520)

        # Предпросмотр письма (правая колонка)
        preview = ttk.LabelFrame(root, text="Предпросмотр письма",
                                 style="Card.TLabelframe", padding=12)
        preview.grid(row=0, column=1, rowspan=7, sticky="nsew", padx=(0, 10), pady=10)
        preview.grid_columnconfigure(0, weight=1)
        preview.grid_columnconfigure(1, weight=1)
        preview.grid_rowconfigure(2, weight=1)

        ttk.Label(preview, text=f"Тестовое ФИО: {self.preview_fio}")\
            .grid(row=0, column=0, sticky="w", padx=5, pady=(0,6))
        self.btn_compose_preview = ttk.Button(
            preview,
            text="Составить тестовое письмо",
            command=self.compose_test_email,
            style="Accent.TButton"
        )
        self.btn_compose_preview.grid(row=0, column=1, sticky="e", padx=5, pady=(0,6))

        ttk.Label(preview, text="E-mail получателя для генерации:")\
            .grid(row=1, column=0, sticky="w", padx=5, pady=(0,6))
        ttk.Entry(preview, textvariable=self.preview_target_email)\
            .grid(row=1, column=1, sticky="we", padx=5, pady=(0,6))

        preview_body = ttk.Frame(preview, style="Card.TFrame")
        preview_body.grid(row=2, column=0, columnspan=2, sticky="nsew", padx=0, pady=(6,0))
        preview_body.grid_columnconfigure(0, weight=1)
        preview_body.grid_rowconfigure(0, weight=1)

        self.preview_text = tk.Text(
            preview_body, height=28, wrap="word",
            bg="#050b1a", fg=UI_TEXT, insertbackground=UI_TEXT,
            relief="solid", borderwidth=1, highlightthickness=0
        )
        self.preview_text.grid(row=0, column=0, sticky="nsew")
        pv_scroll = ttk.Scrollbar(preview_body, orient="vertical", command=self.preview_text.yview)
        pv_scroll.grid(row=0, column=1, sticky="ns")
        self.preview_text.configure(yscrollcommand=pv_scroll.set)
        self._set_preview_text("Нажмите «Составить тестовое письмо», чтобы увидеть итог по текущим параметрам.")
        self.btn_open_html = ttk.Button(preview, text="Открыть HTML в браузере",
                                        command=self._open_html_in_browser, style="TButton")
        self.btn_open_html.grid(row=3, column=0, sticky="w", padx=5, pady=(10,0))

        # SMTP (мульти)
        smtp = ttk.LabelFrame(root, text="Отправители (несколько SMTP-аккаунтов)",
                              style="Card.TLabelframe", padding=12)
        smtp.grid(row=0, column=0, sticky="we", padx=10, pady=(10,8))
        smtp.grid_columnconfigure(0, weight=1)
        smtp.grid_columnconfigure(1, weight=1)

        self.smtp_summary_var = tk.StringVar(value="Отправителей: 0")
        ttk.Label(smtp, textvariable=self.smtp_summary_var)\
            .grid(row=0, column=0, sticky="w", padx=5, pady=(4,4))

        btns = ttk.Frame(smtp, style="Card.TFrame")
        btns.grid(row=0, column=1, sticky="e", padx=5, pady=4)
        ttk.Button(btns, text="Управление отправителями…", command=self.open_smtp_manager)\
            .pack(side="left", padx=(0,6))
        ttk.Button(btns, text="Тестовая отправка со всех…", command=self.send_test_all)\
            .pack(side="left")

        # Источники (пул)
        src_frame = ttk.LabelFrame(root, text="Список источников",
                                   style="Card.TLabelframe", padding=12)
        src_frame.grid(row=1, column=0, sticky="nsew", padx=10, pady=(0,8))
        src_frame.grid_columnconfigure(0, weight=1)
        self.sources_summary_var = tk.StringVar(value="Источников: 0 | Контактов: 0")
        ttk.Label(src_frame, textvariable=self.sources_summary_var)\
            .grid(row=0, column=0, sticky="w", padx=5, pady=(6,4))
        src_btns = ttk.Frame(src_frame, style="Card.TFrame")
        src_btns.grid(row=1, column=0, sticky="we", padx=5, pady=(0,6))
        ttk.Button(src_btns, text="Управление источниками…", command=self.open_sources_manager).pack(side="left")
        ttk.Button(src_btns, text="Контакты по источникам…", command=self.open_contacts_manager).pack(side="left", padx=6)

        # Шаблоны
        tpl = ttk.LabelFrame(root, text="Шаблоны писем (слева — с {fio}, справа — без ФИО)",
                             style="Card.TLabelframe", padding=12)
        tpl.grid(row=2, column=0, sticky="nsew", padx=10, pady=(0,8))
        tpl.grid_columnconfigure(1, weight=1)
        tpl.grid_columnconfigure(3, weight=1)
        tpl.grid_rowconfigure(2, weight=1)

        ttk.Label(tpl, text="Тема (с ФИО):").grid(row=0, column=0, sticky="nw", padx=5, pady=5)
        ttk.Entry(tpl, textvariable=self.subject_tpl).grid(row=0, column=1, sticky="we", padx=5, pady=5)

        ttk.Label(tpl, text="Тема (без ФИО):").grid(row=0, column=2, sticky="nw", padx=5, pady=5)
        ttk.Entry(tpl, textvariable=self.subject_tpl_nofio).grid(row=0, column=3, sticky="we", padx=5, pady=5)

        ttk.Label(tpl, text="Тема рассылки:").grid(row=1, column=0, sticky="nw", padx=5, pady=(0,5))
        ttk.Entry(tpl, textvariable=self.campaign_theme).grid(row=1, column=1, columnspan=3, sticky="we", padx=5, pady=(0,5))

        ttk.Label(tpl, text="Пожелания рассылки:").grid(row=2, column=0, sticky="nw", padx=5, pady=5)
        self.campaign_wishes_text = tk.Text(tpl, height=4, wrap="word",
                                            bg="#0b1222", fg=UI_TEXT,
                                            insertbackground=UI_TEXT, relief="solid",
                                            borderwidth=1, highlightthickness=0)
        self.campaign_wishes_text.grid(row=2, column=1, columnspan=3, sticky="nsew", padx=5, pady=5)
        self._set_campaign_wishes_text(self._campaign_wishes_value)

        ttk.Label(tpl, text="Эти поля будут использоваться для генерации писем через LLM.").grid(
            row=3, column=0, columnspan=4, sticky="w", padx=5, pady=(0,5)
        )

        ttk.Label(tpl, text="Сайт компании (CTA):").grid(row=4, column=0, sticky="e", padx=5, pady=(0,5))
        ttk.Entry(tpl, textvariable=self.company_site).grid(row=4, column=1, columnspan=3, sticky="we", padx=5, pady=(0,5))
        ttk.Label(tpl, text="ID рассылки:").grid(row=5, column=0, sticky="e", padx=5, pady=(0,5))
        ttk.Entry(tpl, textvariable=self.mailing_id).grid(row=5, column=1, columnspan=3, sticky="we", padx=5, pady=(0,5))

        # Вложения
        att = ttk.LabelFrame(root, text="Вложения", style="Card.TLabelframe", padding=12)
        att.grid(row=3, column=0, sticky="nsew", padx=10, pady=(0,8))
        att.grid_columnconfigure(0, weight=1)
        self.attach_list = tk.Listbox(att, height=4, selectmode="extended",
                                      bg="#0b1222", fg=UI_TEXT,
                                      highlightthickness=0, borderwidth=1,
                                      selectbackground=UI_ACCENT, selectforeground="#ffffff")
        self.attach_list.grid(row=0, column=0, columnspan=3, sticky="nsew", padx=5, pady=5)
        ttk.Button(att, text="Добавить файлы…", command=self.add_attachments)\
            .grid(row=1, column=0, padx=5, pady=5, sticky="w")
        ttk.Button(att, text="Удалить выбранные", command=self.remove_selected_attachments)\
            .grid(row=1, column=1, padx=5, pady=5, sticky="w")
        ttk.Button(att, text="Очистить", command=self.clear_attachments)\
            .grid(row=1, column=2, padx=5, pady=5, sticky="w")
        ttk.Label(att, text="Описание вложений (LLM):").grid(row=2, column=0, sticky="w", padx=5, pady=(6,2))
        ttk.Entry(att, textvariable=self.attachments_description).grid(row=2, column=1, columnspan=2, sticky="we", padx=5, pady=(6,2))

        # Расписание
        # --- Расписание ---
        sched = ttk.LabelFrame(root, text="Расписание (авто-запуск один раз в день, когда приложение открыто)",
                               style="Card.TLabelframe", padding=12)
        sched.grid(row=4, column=0, sticky="we", padx=10, pady=(0,8))
        # Ничего не растягиваем, чтобы правый край не «утягивал» контролы вправо
        for c in range(12):
            sched.grid_columnconfigure(c, weight=0)

        self._schedule_controls = []  # type: List[tk.Widget]

        ttk.Checkbutton(sched, text="Включить расписание", variable=self.schedule_enabled)\
            .grid(row=0, column=0, sticky="w", padx=8, pady=(6,4), columnspan=8)

        # Дни недели (1..7 — чтобы слева была колонка для меток)
        days = ["Пн","Вт","Ср","Чт","Пт","Сб","Вс"]
        day_checks = []
        for i, d in enumerate(days, start=1):
            chk = ttk.Checkbutton(sched, text=d, variable=self.schedule_days_vars[i-1])
            chk.grid(row=1, column=i, sticky="w", padx=4, pady=(0,6))
            day_checks.append(chk)
        self._schedule_controls.extend(day_checks)

        # Время по дням
        ttk.Label(sched, text="Время:").grid(row=2, column=0, sticky="e", padx=5)
        time_entries = []
        for i in range(7):
            ent = ttk.Entry(sched, width=6, textvariable=self.schedule_times[i])
            ent.grid(row=2, column=i+1, sticky="w", padx=2)
            time_entries.append(ent)
        self._schedule_controls.extend(time_entries)

        # Случайный дрейф — отдельный левый фрейм, чтобы не «плавал» вправо
        drift = ttk.Frame(sched, style="Card.TFrame")
        drift.grid(row=3, column=1, columnspan=7, sticky="w", padx=8, pady=(6,6))

        chk_drift = ttk.Checkbutton(drift, text="Случайный дрейф запуска (± минут)", variable=self.rand_time_enabled)
        chk_drift.pack(side="left")
        self._schedule_controls.append(chk_drift)

        ttk.Label(drift, text="от:").pack(side="left", padx=(12,4))
        sp_from = ttk.Spinbox(drift, from_=0, to=600, width=5, textvariable=self.rand_time_min)
        sp_from.pack(side="left")
        ttk.Label(drift, text="до:").pack(side="left", padx=(8,4))
        sp_to = ttk.Spinbox(drift, from_=0, to=600, width=5, textvariable=self.rand_time_max)
        sp_to.pack(side="left")
        self._schedule_controls.extend([sp_from, sp_to])


        # Параметры отправки
        ctrl = ttk.LabelFrame(root, text="Параметры отправки",
                              style="Card.TLabelframe", padding=12)
        ctrl.grid(row=5, column=0, sticky="we", padx=10, pady=(0,8))
        for c in range(10):
            ctrl.grid_columnconfigure(c, weight=0)
        ctrl.grid_columnconfigure(1, weight=1)

        ttk.Label(ctrl, text="Фикс. задержка (сек):").grid(row=0, column=0, sticky="w", padx=5, pady=5)
        self.spin_delay = ttk.Spinbox(ctrl, from_=0, to=3600, textvariable=self.delay_sec, width=8)
        self.spin_delay.grid(row=0, column=1, sticky="w", padx=5, pady=5)

        ttk.Checkbutton(ctrl, text="Случайная задержка", variable=self.random_delay_enabled,
                        command=self._update_controls_state)\
            .grid(row=0, column=2, sticky="w", padx=10, pady=5)
        ttk.Label(ctrl, text="от").grid(row=0, column=3, sticky="e")
        self.spin_delay_min = ttk.Spinbox(ctrl, from_=0, to=3600, textvariable=self.delay_min, width=6)
        self.spin_delay_min.grid(row=0, column=4, sticky="w", padx=2)
        ttk.Label(ctrl, text="до").grid(row=0, column=5, sticky="e")
        self.spin_delay_max = ttk.Spinbox(ctrl, from_=0, to=3600, textvariable=self.delay_max, width=6)
        self.spin_delay_max.grid(row=0, column=6, sticky="w", padx=2)

        ttk.Label(ctrl, text="Лимит писем за запуск (на аккаунт):").grid(row=1, column=0, sticky="w", padx=5, pady=5)
        self.spin_limit = ttk.Spinbox(ctrl, from_=1, to=10000, textvariable=self.limit_count, width=8)
        self.spin_limit.grid(row=1, column=1, sticky="w", padx=5, pady=5)

        ttk.Checkbutton(ctrl, text="Случайный дневной лимит", variable=self.random_limit_enabled,
                        command=self._update_controls_state)\
            .grid(row=1, column=2, sticky="w", padx=10, pady=5)
        ttk.Label(ctrl, text="от").grid(row=1, column=3, sticky="e")
        self.spin_lmin = ttk.Spinbox(ctrl, from_=1, to=100000, textvariable=self.limit_min, width=8)
        self.spin_lmin.grid(row=1, column=4, sticky="w", padx=2)
        ttk.Label(ctrl, text="до").grid(row=1, column=5, sticky="e")
        self.spin_lmax = ttk.Spinbox(ctrl, from_=1, to=100000, textvariable=self.limit_max, width=8)
        self.spin_lmax.grid(row=1, column=6, sticky="w", padx=2)

        ttk.Checkbutton(ctrl, text="Попарное сопоставление ФИО ↔ e-mail (если включено)",
                        variable=self.pair_mode)\
            .grid(row=2, column=0, columnspan=6, sticky="w", padx=5, pady=5)

        # Лог
        log_frame = ttk.LabelFrame(root, text="Лог", style="Card.TLabelframe", padding=12)
        log_frame.grid(row=6, column=0, sticky="nsew", padx=10, pady=(0,10))
        root.grid_rowconfigure(6, weight=1)
        root.grid_columnconfigure(0, weight=3)
        root.grid_columnconfigure(1, weight=4)
        self.log = tk.Text(log_frame, height=18, wrap="word", state="disabled",
                           bg="#050b1a", fg=UI_TEXT, insertbackground=UI_TEXT,
                           borderwidth=0, highlightthickness=0)
        self.log.pack(fill="both", expand=True, padx=5, pady=5)


    # --- Менеджеры: SMTP / Источники / Контакты ---
    def open_smtp_manager(self):
        win = tk.Toplevel(self)
        win.title("Отправители SMTP")
        win.geometry("860x420+140+80")
        win.grab_set()

        columns = ("id", "email", "host", "port", "security", "from_name", "source")
        tree = ttk.Treeview(win, columns=columns, show="headings", height=12)
        for col, text, w in [
            ("id", "ID", 50),
            ("email", "E-mail", 200),
            ("host", "Host", 160),
            ("port", "Port", 70),
            ("security", "Security", 80),
            ("from_name", "От имени", 180),
            ("source", "Источник", 100),
        ]:
            tree.heading(col, text=text)
            tree.column(col, width=w, stretch=(col in ("email","from_name","host")))
        tree.pack(side="top", fill="both", expand=True, padx=8, pady=(8,4))

        btns = ttk.Frame(win)
        btns.pack(side="top", fill="x", padx=8, pady=4)
        ttk.Button(btns, text="Добавить…", command=lambda: self._smtp_open_form(win, tree)).pack(side="left")
        ttk.Button(btns, text="Изменить…", command=lambda: self._smtp_open_form(win, tree, edit=True)).pack(side="left", padx=6)
        ttk.Button(btns, text="Удалить", command=lambda: self._smtp_delete_selected(tree)).pack(side="left", padx=6)

        def refresh():
            for i in tree.get_children():
                tree.delete(i)
            sources = {s["id"]: s for s in self._list_sources()}
            for acc in self._list_smtp_accounts():
                src_label = "-"
                if acc.get("source_id") and acc["source_id"] in sources:
                    src_label = f'ID {acc["source_id"]}'
                tree.insert("", "end", values=(
                    acc["id"], acc["email"], acc["host"], acc["port"], acc["security"],
                    acc.get("from_name",""), src_label
                ))
            self._refresh_db_summaries()
        refresh()
        tree.refresh = refresh  # type: ignore
        win.bind("<Escape>", lambda e: win.destroy())

    def _smtp_delete_selected(self, tree: ttk.Treeview):
        sel = tree.selection()
        if not sel:
            return
        if not messagebox.askyesno(APP_NAME, "Удалить выбранные SMTP-аккаунты?"):
            return
        for it in sel:
            vals = tree.item(it, "values")
            if not vals:
                continue
            self._delete_smtp_account(int(vals[0]))
        tree.refresh()

    def _smtp_open_form(self, parent, tree: ttk.Treeview, edit: bool=False):
        sources = self._list_sources()
        src_choices = ["(не выбран)"] + [f'ID {s["id"]}: {Path(s["path"]).name}' for s in sources]

        sel_values = None
        if edit:
            sel = tree.selection()
            if not sel:
                messagebox.showinfo(APP_NAME, "Выберите строку для редактирования.")
                return
            sel_values = tree.item(sel[0], "values")
            if not sel_values:
                return

        win = tk.Toplevel(parent)
        win.title("SMTP аккаунт" + (" (редактирование)" if edit else ""))
        win.geometry("520x380+180+120")
        win.grab_set()

        labels = [
            ("E-mail", 0), ("Пароль", 1),
            ("Host", 2), ("Port", 3),
            ("Security (SSL/STARTTLS/PLAIN)", 4),
            ("От имени", 5),
            ("Источник (src)", 6),
        ]
        entries = {}
        for text, row in labels:
            ttk.Label(win, text=text).grid(row=row, column=0, sticky="e", padx=8, pady=6)
        email_var = tk.StringVar()
        pwd_var = tk.StringVar()
        host_var = tk.StringVar()
        port_var = tk.IntVar(value=465)
        sec_var = tk.StringVar(value="SSL")
        from_var = tk.StringVar()
        src_var = tk.StringVar(value=src_choices[0])

        ttk.Entry(win, textvariable=email_var, width=34).grid(row=0, column=1, padx=8, pady=6, sticky="we")
        ttk.Entry(win, textvariable=pwd_var, width=34, show="*").grid(row=1, column=1, padx=8, pady=6, sticky="we")
        ttk.Entry(win, textvariable=host_var, width=34).grid(row=2, column=1, padx=8, pady=6, sticky="we")
        ttk.Entry(win, textvariable=port_var, width=12).grid(row=3, column=1, padx=8, pady=6, sticky="w")
        ttk.Combobox(win, textvariable=sec_var, values=["SSL","STARTTLS","PLAIN"], width=12, state="readonly")\
            .grid(row=4, column=1, padx=8, pady=6, sticky="w")
        ttk.Entry(win, textvariable=from_var, width=34).grid(row=5, column=1, padx=8, pady=6, sticky="we")
        ttk.Combobox(win, textvariable=src_var, values=src_choices, state="readonly")\
            .grid(row=6, column=1, padx=8, pady=6, sticky="we")

        for i in range(2):
            win.grid_columnconfigure(i, weight=1)

        acc_id = None
        if sel_values:
            acc_id = int(sel_values[0])
            email_var.set(sel_values[1])
            host_var.set(sel_values[2])
            port_var.set(int(sel_values[3]))
            sec_var.set(sel_values[4])
            from_var.set(sel_values[5])
            # source selection
            src_label = sel_values[6] or "(не выбран)"
            if src_label in src_choices:
                src_var.set(src_label)

        def on_save():
            email = email_var.get().strip()
            pwd = pwd_var.get()
            host = host_var.get().strip()
            sec = sec_var.get().strip()
            try:
                port = int(port_var.get())
            except Exception:
                messagebox.showerror(APP_NAME, "Некорректный порт.")
                return
            if not email or not host:
                messagebox.showerror(APP_NAME, "Заполните email и host.")
                return
            src_id = None
            if src_var.get() != "(не выбран)":
                try:
                    src_id = int(src_var.get().split()[1])
                except Exception:
                    src_id = None
            rec = dict(id=acc_id, email=email, password=pwd, host=host,
                       port=port, security=sec, from_name=from_var.get().strip(),
                       source_id=src_id)
            self._upsert_smtp_account(rec)
            win.destroy()
            tree.refresh()
        ttk.Button(win, text="Сохранить", command=on_save, style="Accent.TButton")\
            .grid(row=7, column=1, sticky="e", padx=8, pady=12)

    def open_sources_manager(self):
        win = tk.Toplevel(self)
        win.title("Источники данных")
        win.geometry("900x460+120+80")
        win.grab_set()

        columns = ("id", "path", "start_row", "email_col", "fio_from", "fio_to")
        tree = ttk.Treeview(win, columns=columns, show="headings", height=14)
        for col, text, w in [
            ("id", "ID", 50),
            ("path", "Путь", 520),
            ("start_row", "Старт", 60),
            ("email_col", "E-mail", 70),
            ("fio_from", "ФИО c", 70),
            ("fio_to", "ФИО по", 70),
        ]:
            tree.heading(col, text=text)
            tree.column(col, width=w, stretch=(col=="path"))
        tree.pack(side="top", fill="both", expand=True, padx=8, pady=(8,4))

        btns = ttk.Frame(win)
        btns.pack(side="top", fill="x", padx=8, pady=4)
        ttk.Button(btns, text="Добавить…", command=lambda: self._source_open_form(win, tree)).pack(side="left")
        ttk.Button(btns, text="Изменить…", command=lambda: self._source_open_form(win, tree, edit=True)).pack(side="left", padx=6)
        ttk.Button(btns, text="Удалить", command=lambda: self._source_delete_selected(tree)).pack(side="left", padx=6)
        ttk.Button(btns, text="Импорт контактов", command=lambda: self._import_contacts_selected(tree)).pack(side="right")

        def refresh():
            for i in tree.get_children():
                tree.delete(i)
            for s in self._list_sources():
                tree.insert("", "end", values=(s["id"], s["path"], s["start_row"], s["email_col"], s["fio_from"], s["fio_to"]))
            self._refresh_db_summaries()
        refresh()
        tree.refresh = refresh  # type: ignore
        win.bind("<Escape>", lambda e: win.destroy())

    def _source_delete_selected(self, tree: ttk.Treeview):
        sel = tree.selection()
        if not sel:
            return
        if not messagebox.askyesno(APP_NAME, "Удалить выбранные источники?"):
            return
        for it in sel:
            vals = tree.item(it, "values")
            if not vals:
                continue
            self._delete_source(int(vals[0]))
        tree.refresh()

    def _source_open_form(self, parent, tree: ttk.Treeview, edit: bool=False):
        sel_values = None
        if edit:
            sel = tree.selection()
            if not sel:
                messagebox.showinfo(APP_NAME, "Выберите строку для редактирования.")
                return
            sel_values = tree.item(sel[0], "values")
            if not sel_values:
                return

        win = tk.Toplevel(parent)
        win.title("Источник" + (" (редактирование)" if edit else ""))
        win.geometry("640x320+180+140")
        win.grab_set()

        path_var = tk.StringVar()
        start_var = tk.IntVar(value=self.def_start_row.get())
        email_var = tk.IntVar(value=self.def_email_col.get())
        fio_from_var = tk.IntVar(value=self.def_fio_from.get())
        fio_to_var = tk.IntVar(value=self.def_fio_to.get())

        ttk.Label(win, text="Путь к файлу").grid(row=0, column=0, sticky="e", padx=8, pady=6)
        path_entry = ttk.Entry(win, textvariable=path_var, width=48)
        path_entry.grid(row=0, column=1, padx=8, pady=6, sticky="we")
        ttk.Button(win, text="…", width=4, command=lambda: self._pick_source_path(path_var)).grid(row=0, column=2, padx=4, pady=6)

        ttk.Label(win, text="Стартовая строка").grid(row=1, column=0, sticky="e", padx=8, pady=6)
        ttk.Entry(win, textvariable=start_var, width=10).grid(row=1, column=1, sticky="w", padx=8, pady=6)
        ttk.Label(win, text="Колонка e-mail").grid(row=2, column=0, sticky="e", padx=8, pady=6)
        ttk.Entry(win, textvariable=email_var, width=10).grid(row=2, column=1, sticky="w", padx=8, pady=6)
        ttk.Label(win, text="ФИО c").grid(row=3, column=0, sticky="e", padx=8, pady=6)
        ttk.Entry(win, textvariable=fio_from_var, width=10).grid(row=3, column=1, sticky="w", padx=8, pady=6)
        ttk.Label(win, text="ФИО по").grid(row=4, column=0, sticky="e", padx=8, pady=6)
        ttk.Entry(win, textvariable=fio_to_var, width=10).grid(row=4, column=1, sticky="w", padx=8, pady=6)

        for i in range(3):
            win.grid_columnconfigure(i, weight=1)

        src_id = None
        if sel_values:
            src_id = int(sel_values[0])
            path_var.set(sel_values[1])
            start_var.set(int(sel_values[2]))
            email_var.set(int(sel_values[3]))
            fio_from_var.set(int(sel_values[4]))
            fio_to_var.set(int(sel_values[5]))

        def on_save():
            path = path_var.get().strip()
            if not path:
                messagebox.showerror(APP_NAME, "Укажите путь к файлу.")
                return
            try:
                rec = dict(
                    id=src_id,
                    path=path,
                    start_row=int(start_var.get()),
                    email_col=int(email_var.get()),
                    fio_from=int(fio_from_var.get()),
                    fio_to=int(fio_to_var.get()),
                )
            except Exception:
                messagebox.showerror(APP_NAME, "Проверьте числовые поля.")
                return
            self._upsert_source(rec)
            win.destroy()
            tree.refresh()
        ttk.Button(win, text="Сохранить", command=on_save, style="Accent.TButton")\
            .grid(row=5, column=2, sticky="e", padx=8, pady=12)

    def _pick_source_path(self, var: tk.StringVar):
        path = filedialog.askopenfilename(
            title="Выберите Excel/CSV файл",
            filetypes=[("Excel/CSV", "*.xlsx *.xls *.csv"), ("Все файлы", "*.*")]
        )
        if path:
            var.set(path)

    def _import_contacts_selected(self, tree: ttk.Treeview):
        sel = tree.selection()
        if not sel:
            messagebox.showinfo(APP_NAME, "Выберите источник для импорта.")
            return
        vals = tree.item(sel[0], "values")
        if not vals:
            return
        src_id = int(vals[0])
        self._import_contacts_from_source(src_id)
        tree.refresh()

    def _import_contacts_from_source(self, src_id: int):
        src = self._get_source_by_id(src_id)
        if not src:
            messagebox.showerror(APP_NAME, "Источник не найден.")
            return
        path = src["path"]
        if not Path(path).exists():
            messagebox.showerror(APP_NAME, f"Файл не найден: {path}")
            return
        try:
            df = read_table(path, start_row=int(src["start_row"]))
        except Exception as e:
            messagebox.showerror(APP_NAME, f"Ошибка чтения файла: {e}")
            return
        pairs: List[Tuple[str, str]] = []
        for _, row in df.iterrows():
            emails = self._pick_emails_from_row_with_cols(row, src["email_col"])
            best_fio, _, _ = self._pick_fio_best_from_row_with_cols(row, src["fio_from"], src["fio_to"])
            if emails:
                fio_val = best_fio or ""
                for em in emails:
                    pairs.append((em, fio_val))
        self._remember_contacts(src_id, pairs)
        messagebox.showinfo(APP_NAME, f"Импортировано контактов: {len(pairs)}")
        self._refresh_db_summaries()

    def open_contacts_manager(self):
        win = tk.Toplevel(self)
        win.title("Контакты по источникам")
        win.geometry("640x500+150+90")
        win.grab_set()

        sources = self._list_sources()
        src_var = tk.StringVar(value="(выберите источник)")
        choices = ["(выберите источник)"] + [f'ID {s["id"]}: {Path(s["path"]).name}' for s in sources]
        ttk.Combobox(win, textvariable=src_var, values=choices, state="readonly")\
            .pack(side="top", fill="x", padx=10, pady=(10,6))

        columns = ("id","email","fio")
        tree = ttk.Treeview(win, columns=columns, show="headings", height=18)
        for col, text, w in [("id","ID",50), ("email","E-mail",240), ("fio","ФИО",280)]:
            tree.heading(col, text=text)
            tree.column(col, width=w, stretch=(col!="id"))
        tree.pack(side="top", fill="both", expand=True, padx=10, pady=(4,10))

        def refresh_tree():
            for i in tree.get_children():
                tree.delete(i)
            sel = src_var.get()
            if sel.startswith("ID "):
                try:
                    sid = int(sel.split()[1].rstrip(":"))
                except Exception:
                    return
                for c in self._list_contacts(sid):
                    tree.insert("", "end", values=(c["id"], c["email"], c["fio"]))

        def on_change(_e=None):
            refresh_tree()
        src_var.trace_add("write", lambda *args: on_change())

        win.bind("<Escape>", lambda e: win.destroy())
        refresh_tree()

    def _refresh_db_summaries(self):
        accs = self._list_smtp_accounts()
        sources = self._list_sources()
        contacts_total = 0
        try:
            rows = self._db_fetchall("SELECT COUNT(*) FROM contact")
            if rows:
                contacts_total = int(rows[0][0])
        except Exception:
            contacts_total = 0
        if hasattr(self, "smtp_summary_var"):
            self.smtp_summary_var.set(f"Отправителей: {len(accs)}")
        if hasattr(self, "sources_summary_var"):
            self.sources_summary_var.set(f"Источников: {len(sources)} | Контактов: {contacts_total}")

    # --- Контекстное меню / буфер ---
    def _install_clipboard_features(self):
        classes = ("Entry", "TEntry", "Text")
        def bind_all(cls, sequence, func):
            self.bind_class(cls, sequence, func, add="+")
        for cls in classes:
            bind_all(cls, "<Control-c>", lambda e: (e.widget.event_generate("<<Copy>>"), "break"))
            bind_all(cls, "<Control-x>", lambda e: (e.widget.event_generate("<<Cut>>"), "break"))
            bind_all(cls, "<Control-v>", lambda e: (e.widget.event_generate("<<Paste>>"), "break"))
            bind_all(cls, "<Control-a>", self._select_all_key)
            bind_all(cls, "<Shift-Insert>", lambda e: (e.widget.event_generate("<<Paste>>"), "break"))
            bind_all(cls, "<Control-Insert>", lambda e: (e.widget.event_generate("<<Copy>>"), "break"))
        for cls in classes:
            bind_all(cls, "<Command-c>", lambda e: (e.widget.event_generate("<<Copy>>"), "break"))
            bind_all(cls, "<Command-x>", lambda e: (e.widget.event_generate("<<Cut>>"), "break"))
            bind_all(cls, "<Command-v>", lambda e: (e.widget.event_generate("<<Paste>>"), "break"))
            bind_all(cls, "<Command-a>", self._select_all_key)

        self._ctx_menu = tk.Menu(self, tearoff=0)
        self._ctx_menu.add_command(label="Вырезать", command=lambda: self._ctx_action("<<Cut>>"))
        self._ctx_menu.add_command(label="Копировать", command=lambda: self._ctx_action("<<Copy>>"))
        self._ctx_menu.add_command(label="Вставить", command=lambda: self._ctx_action("<<Paste>>"))
        self._ctx_menu.add_separator()
        self._ctx_menu.add_command(label="Выделить всё", command=self._select_all_focus)

        def show_menu(event):
            widget = event.widget
            if widget.winfo_class() in ("Entry", "TEntry", "Text"):
                try:
                    self._ctx_menu.tk_popup(event.x_root, event.y_root)
                finally:
                    self._ctx_menu.grab_release()
            return "break"

        for cls in classes:
            self.bind_class(cls, "<Button-3>", show_menu, add="+")
            self.bind_class(cls, "<Button-2>", show_menu, add="+")  # совместимость

    def _restyle_all_buttons(self):
        def walk(widget):
            for child in widget.winfo_children():
                if isinstance(child, ttk.Button):
                    style = child.cget("style") or ""
                    if style in ("", "TButton"):
                        child.configure(style="TButton")
                walk(child)
        walk(self)

    def _ctx_action(self, virtual_event: str):
        w = self.focus_get()
        if w and w.winfo_class() in ("Entry","TEntry","Text"):
            try:
                w.event_generate(virtual_event)
            except Exception:
                pass

    def _set_campaign_wishes_text(self, value: str):
        self._campaign_wishes_value = value or ""
        if hasattr(self, "campaign_wishes_text"):
            self.campaign_wishes_text.delete("1.0", "end")
            if self._campaign_wishes_value:
                self.campaign_wishes_text.insert("1.0", self._campaign_wishes_value)

    def _get_campaign_wishes(self) -> str:
        if hasattr(self, "campaign_wishes_text"):
            text = self.campaign_wishes_text.get("1.0", "end-1c").strip()
        else:
            text = self._campaign_wishes_value
        self._campaign_wishes_value = text
        return text

    def _set_preview_text(self, text: str):
        if not hasattr(self, "preview_text"):
            return
        self.preview_text.configure(state="normal")
        self.preview_text.delete("1.0", "end")
        clean = (text or "").rstrip()
        self.preview_text.insert("1.0", clean + ("\n" if clean else ""))
        self.preview_text.configure(state="disabled")

    def _render_html_preview(self, html_content: Optional[str]):
        self.preview_last_html = html_content or ""

    def _open_html_in_browser(self):
        if not self.preview_last_html:
            messagebox.showinfo(APP_NAME, "Сначала сгенерируйте письмо.")
            return
        try:
            with tempfile.NamedTemporaryFile("w", delete=False, suffix=".html", encoding="utf-8") as f:
                f.write(self.preview_last_html)
                path = f.name
            webbrowser.open(f"file://{path}")
        except Exception as e:
            messagebox.showerror(APP_NAME, f"Не удалось открыть HTML: {e}")

    def _load_llm_template(self) -> Optional[str]:
        try:
            return LLM_TEMPLATE_FILE.read_text(encoding="utf-8")
        except FileNotFoundError:
            self.append_log(f"[LLM] Шаблон {LLM_TEMPLATE_FILE.name} не найден.")
        except Exception as e:
            self.append_log(f"[LLM] Ошибка чтения шаблона: {e}")
        return None

    def _ollama_generate(self, prompt: str) -> Optional[str]:
        payload = {
            "model": OLLAMA_MODEL,
            "prompt": prompt,
            "stream": False,
            "format": {
                "type": "object",
                "additionalProperties": False,
                "required": [
                    "subject","preheader","brand_name","brand_tagline","headline1","headline2",
                    "intro_text","updates_title","updates_item_1","updates_item_2","updates_item_3"
                ],
                "properties": {
                    "subject": {"type": "string"},
                    "preheader": {"type": "string"},
                    "brand_name": {"type": "string"},
                    "brand_tagline": {"type": "string"},
                    "headline1": {"type": "string"},
                    "headline2": {"type": "string"},
                    "intro_text": {"type": "string"},
                    "updates_title": {"type": "string"},
                    "updates_item_1": {"type": "string"},
                    "updates_item_2": {"type": "string"},
                    "updates_item_3": {"type": "string"},
                },
            },
        }
        data = json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            OLLAMA_URL.rstrip("/") + "/api/generate",
            data=data,
            headers={"Content-Type": "application/json"},
            method="POST"
        )
        try:
            with urllib.request.urlopen(req, timeout=120) as resp:
                raw = resp.read().decode("utf-8")
        except urllib.error.URLError as e:
            self.append_log(f"[LLM] Ошибка запроса Ollama: {e}")
            return None
        except Exception as e:
            self.append_log(f"[LLM] Не удалось обратиться к Ollama: {e}")
            return None
        try:
            obj = json.loads(raw)
        except Exception:
            self.append_log("[LLM] Некорректный ответ от Ollama (не JSON).")
            return None
        return (obj.get("response") or "").strip()

    def _extract_json_fields(self, text: str) -> Optional[Dict[str, str]]:
        if not text:
            return None
        text = text.strip()
        candidate = text
        if not text.startswith("{"):
            start = text.find("{")
            end = text.rfind("}")
            if start != -1 and end != -1 and end > start:
                candidate = text[start:end+1]
        try:
            data = json.loads(candidate)
        except Exception:
            self.append_log(f"[LLM] Не удалось распарсить JSON из ответа Ollama. Сырой ответ: {text[:500]}")
            return None
        if not isinstance(data, dict):
            self.append_log("[LLM] Ответ Ollama не содержит JSON-объект.")
            return None
        cleaned = {}
        for field in LLM_PLACEHOLDERS:
            val = data.get(field, "")
            cleaned[field] = str(val).strip()
        return cleaned

    def _fill_llm_template(self, fields: Dict[str, str]) -> Optional[str]:
        if not self.llm_template:
            self.llm_template = self._load_llm_template()
        template = self.llm_template
        if not template:
            return None
        html_body = template
        for key in LLM_PLACEHOLDERS:
            value = html.escape(fields.get(key, ""), quote=False)
            html_body = html_body.replace(f"{{{{{key}}}}}", value)
        # совместимость: если шаблон содержит {headline}, подставим headline1
        html_body = html_body.replace("{{headline}}", html.escape(fields.get("headline1", ""), quote=False))
        cta_url = getattr(self, "company_site", tk.StringVar(value="https://example.com")).get()
        html_body = html_body.replace("{{cta_url}}", html.escape(cta_url, quote=True))
        return html_body

    @staticmethod
    def _plain_from_fields(fields: Dict[str, str]) -> str:
        parts: List[str] = []
        h1 = fields.get("headline1") or fields.get("headline")
        h2 = fields.get("headline2", "")
        if h1:
            parts.append(h1)
        if h2:
            parts.append(h2)
        if fields.get("intro_text"):
            if parts:
                parts.append("")
            parts.append(fields["intro_text"])
        if fields.get("updates_title"):
            parts.append("")
            parts.append(fields["updates_title"])
            for key in ("updates_item_1", "updates_item_2", "updates_item_3"):
                val = fields.get(key)
                if val:
                    parts.append(f"- {val}")
        if fields.get("brand_name") or fields.get("brand_tagline"):
            parts.append("")
            brand_line = fields.get("brand_name", "")
            tagline = fields.get("brand_tagline")
            if tagline:
                brand_line = f"{brand_line} — {tagline}".strip(" —")
            if brand_line:
                parts.append(brand_line)
        return "\n".join(part for part in parts if part is not None)

    @staticmethod
    def _format_email_date(value: str) -> str:
        raw = (value or "").strip()
        if not raw:
            return ""
        try:
            iso = raw.replace(" ", "")
            if iso.endswith("Z"):
                iso = iso[:-1] + "+00:00"
            dt = datetime.fromisoformat(iso)
            months = {
                1: "января", 2: "февраля", 3: "марта", 4: "апреля",
                5: "мая", 6: "июня", 7: "июля", 8: "августа",
                9: "сентября", 10: "октября", 11: "ноября", 12: "декабря",
            }
            month = months.get(dt.month, dt.strftime("%b"))
            return f"{dt.day} {month} {dt.year}"
        except Exception:
            return raw

    def _format_llm_fields(self, fields: Dict[str, str]) -> Dict[str, str]:
        # Используем дату формирования письма, а не дату из модели
        fields["email_date"] = datetime.now().strftime("%-d %B %Y") if os.name != "nt" else datetime.now().strftime("%#d %B %Y")
        return fields

    def _build_llm_prompt(self, fio: str, to_email: str) -> str:
        topic = getattr(self, "active_campaign_theme", "") or getattr(self, "active_subject_tpl", "") or "Рассылка"
        wishes = getattr(self, "active_campaign_wishes", "") or "без дополнительных пожеланий"
        attachments_descr = getattr(self, "active_attachments_description", "") or ""
        fio_txt = fio or "коллега"
        return (
            "email_type: outbound marketing promo\n"
            f"full_name: {fio_txt}\n"
            f"email: {to_email}\n"
            f"topic: {topic}\n"
            f"extra_info: {wishes}\n"
            f"attachments_description: {attachments_descr or 'нет вложений'}\n"
        )

    def _generate_llm_email(self, fio: str, to_email: str) -> Tuple[Optional[str], Optional[str]]:
        prompt = self._build_llm_prompt(fio, to_email)
        response_text = self._ollama_generate(prompt)
        if not response_text:
            return None, None
        fields = self._extract_json_fields(response_text)
        if not fields:
            return None, None
        fields = self._format_llm_fields(fields)
        html_body = self._fill_llm_template(fields)
        if not html_body:
            return None, None
        plain_body = self._plain_from_fields(fields)
        return html_body, plain_body

    def _select_all_key(self, e):
        w = e.widget
        if isinstance(w, tk.Text):
            w.tag_add("sel", "1.0", "end-1c")
        else:
            try:
                w.selection_range(0, "end")
            except Exception:
                pass
        return "break"

    def _select_all_focus(self):
        w = self.focus_get()
        if isinstance(w, tk.Text):
            w.tag_add("sel", "1.0", "end-1c")
        elif isinstance(w, (tk.Entry, ttk.Entry)):
            try:
                w.selection_range(0, "end")
            except Exception:
                pass

    # --- Вложения ---
    def add_attachments(self):
        paths = filedialog.askopenfilenames(
            title="Выберите файлы для вложений",
            filetypes=[("Любые файлы", "*.*")]
        )
        if not paths:
            return
        added = 0
        for p in paths:
            p = str(p)
            if p not in self.attachments:
                self.attachments.append(p)
                if hasattr(self, "attach_list"):
                    self.attach_list.insert("end", p)
                added += 1
        if added:
            self.status_var.set(f"Добавлено вложений: {added}")

    def remove_selected_attachments(self):
        if not hasattr(self, "attach_list"):
            return
        sel = list(self.attach_list.curselection())
        sel.reverse()
        removed = 0
        for idx in sel:
            path = self.attach_list.get(idx)
            if path in self.attachments:
                self.attachments.remove(path)
            self.attach_list.delete(idx)
            removed += 1
        if removed:
            self.status_var.set(f"Удалено вложений: {removed}")

    def clear_attachments(self):
        self.attachments.clear()
        if hasattr(self, "attach_list"):
            self.attach_list.delete(0, "end")
        self.status_var.set("Список вложений очищен")

    # --- Антидубль ---
    def _load_sent_emails(self):
        try:
            if self.sent_list_file.exists():
                with open(self.sent_list_file, "r", encoding="utf-8") as f:
                    for line in f:
                        e = line.strip().lower()
                        if e and EMAIL_REGEX.fullmatch(e):
                            self.sent_emails.add(e)
        except Exception as e:
            self.append_log(f"[АНТИДУБЛЬ] Ошибка чтения {self.sent_list_file.name}: {e}")

    def _add_sent_email(self, email: str):
        e = (email or "").strip().lower()
        if not EMAIL_REGEX.fullmatch(e):
            return
        with self.sent_lock:
            if e in self.sent_emails:
                return
            try:
                with open(self.sent_list_file, "a", encoding="utf-8") as f:
                    f.write(e + "\n")
                self.sent_emails.add(e)
            except Exception as ex:
                self.append_log(f"[АНТИДУБЛЬ] Не удалось записать '{e}': {ex}")

    def _init_sent_db(self):
        try:
            with sqlite3.connect(self.sent_db_path) as conn:
                conn.execute(
                    """
                    CREATE TABLE IF NOT EXISTS sent_mail_log (
                        id INTEGER PRIMARY KEY AUTOINCREMENT,
                        email TEXT NOT NULL,
                        fio TEXT,
                        mailing_id TEXT NOT NULL
                    )
                    """
                )
        except Exception as e:
            self.append_log(f"[БД] Ошибка инициализации лога отправок: {e}")

    def _log_sent_email_db(self, email: str, fio: str):
        mailing_id = getattr(self, "active_mailing_id", "").strip()
        if not mailing_id or not email:
            return
        try:
            with self.sent_db_lock:
                with sqlite3.connect(self.sent_db_path) as conn:
                    conn.execute(
                        "INSERT INTO sent_mail_log (email, fio, mailing_id) VALUES (?, ?, ?)",
                        (email.strip().lower(), fio or "", mailing_id)
                    )
        except Exception as e:
            self.append_log(f"[БД] Ошибка записи отправки {email}: {e}")

    # --- БД: smtp_account / source_file / contact ---
    def _init_app_db(self):
        try:
            with self.sent_db_lock:
                with sqlite3.connect(self.sent_db_path) as conn:
                    conn.execute(
                        """
                        CREATE TABLE IF NOT EXISTS smtp_account (
                            id INTEGER PRIMARY KEY AUTOINCREMENT,
                            email TEXT NOT NULL,
                            password TEXT,
                            host TEXT NOT NULL,
                            port INTEGER NOT NULL,
                            security TEXT NOT NULL,
                            from_name TEXT,
                            source_id INTEGER
                        )
                        """
                    )
                    conn.execute(
                        """
                        CREATE TABLE IF NOT EXISTS source_file (
                            id INTEGER PRIMARY KEY AUTOINCREMENT,
                            path TEXT NOT NULL,
                            start_row INTEGER NOT NULL,
                            email_col INTEGER NOT NULL,
                            fio_from INTEGER NOT NULL,
                            fio_to INTEGER NOT NULL
                        )
                        """
                    )
                    conn.execute(
                        """
                        CREATE TABLE IF NOT EXISTS contact (
                            id INTEGER PRIMARY KEY AUTOINCREMENT,
                            source_id INTEGER,
                            email TEXT NOT NULL,
                            fio TEXT
                        )
                        """
                    )
                    conn.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_contact_source_email ON contact(source_id, email)")
                    conn.execute("CREATE INDEX IF NOT EXISTS idx_smtp_source ON smtp_account(source_id)")
        except Exception as e:
            self.append_log(f"[БД] Ошибка инициализации таблиц: {e}")

    def _db_fetchall(self, query: str, params: Tuple = ()) -> List[Tuple]:
        with self.sent_db_lock:
            with sqlite3.connect(self.sent_db_path) as conn:
                cur = conn.execute(query, params)
                rows = cur.fetchall()
        return rows

    def _db_execute(self, query: str, params: Tuple = ()):
        with self.sent_db_lock:
            with sqlite3.connect(self.sent_db_path) as conn:
                conn.execute(query, params)
                conn.commit()

    def _db_execute_many(self, query: str, rows: List[Tuple]):
        if not rows:
            return
        with self.sent_db_lock:
            with sqlite3.connect(self.sent_db_path) as conn:
                conn.executemany(query, rows)
                conn.commit()

    # --- SMTP accounts ---
    def _list_smtp_accounts(self) -> List[Dict[str, Any]]:
        rows = self._db_fetchall(
            "SELECT id, email, password, host, port, security, from_name, source_id FROM smtp_account ORDER BY id ASC"
        )
        return [
            dict(id=r[0], email=r[1], password=r[2] or "", host=r[3], port=int(r[4]),
                 security=r[5], from_name=r[6] or "", source_id=r[7])
            for r in rows
        ]

    def _upsert_smtp_account(self, rec: Dict[str, Any]):
        if rec.get("id"):
            self._db_execute(
                """UPDATE smtp_account
                   SET email=?, password=?, host=?, port=?, security=?, from_name=?, source_id=?
                   WHERE id=?""",
                (rec["email"], rec.get("password"), rec["host"], int(rec["port"]),
                 rec["security"], rec.get("from_name",""), rec.get("source_id"),
                 int(rec["id"]))
            )
        else:
            self._db_execute(
                """INSERT INTO smtp_account (email, password, host, port, security, from_name, source_id)
                   VALUES (?,?,?,?,?,?,?)""",
                (rec["email"], rec.get("password"), rec["host"], int(rec["port"]),
                 rec["security"], rec.get("from_name",""), rec.get("source_id"))
            )

    def _delete_smtp_account(self, acc_id: int):
        self._db_execute("DELETE FROM smtp_account WHERE id=?", (int(acc_id),))

    # --- Sources ---
    def _list_sources(self) -> List[Dict[str, Any]]:
        rows = self._db_fetchall(
            "SELECT id, path, start_row, email_col, fio_from, fio_to FROM source_file ORDER BY id ASC"
        )
        return [
            dict(id=r[0], path=r[1], start_row=int(r[2]), email_col=int(r[3]),
                 fio_from=int(r[4]), fio_to=int(r[5]))
            for r in rows
        ]

    def _upsert_source(self, rec: Dict[str, Any]):
        if rec.get("id"):
            self._db_execute(
                """UPDATE source_file
                   SET path=?, start_row=?, email_col=?, fio_from=?, fio_to=?
                   WHERE id=?""",
                (rec["path"], int(rec["start_row"]), int(rec["email_col"]),
                 int(rec["fio_from"]), int(rec["fio_to"]), int(rec["id"]))
            )
        else:
            self._db_execute(
                """INSERT INTO source_file (path, start_row, email_col, fio_from, fio_to)
                   VALUES (?,?,?,?,?)""",
                (rec["path"], int(rec["start_row"]), int(rec["email_col"]),
                 int(rec["fio_from"]), int(rec["fio_to"]))
            )

    def _delete_source(self, src_id: int):
        self._db_execute("DELETE FROM source_file WHERE id=?", (int(src_id),))

    # --- Contacts ---
    def _list_contacts(self, source_id: int) -> List[Dict[str, Any]]:
        rows = self._db_fetchall(
            "SELECT id, email, fio FROM contact WHERE source_id=? ORDER BY id ASC",
            (int(source_id),)
        )
        return [dict(id=r[0], email=r[1], fio=r[2] or "") for r in rows]

    def _remember_contacts(self, source_id: Optional[int], pairs: List[Tuple[str, str]]):
        if source_id is None or not pairs:
            return
        rows = []
        for email, fio in pairs:
            if not email:
                continue
            rows.append((int(source_id), email.strip().lower(), fio or ""))
        self._db_execute_many(
            "INSERT OR IGNORE INTO contact (source_id, email, fio) VALUES (?,?,?)",
            rows
        )

    def clear_sent_emails(self):
        if not messagebox.askyesno(APP_NAME, "Очистить список адресов, которым уже отправляли?"):
            return
        with self.sent_lock:
            self.sent_emails.clear()
            try:
                if self.sent_list_file.exists():
                    try:
                        self.sent_list_file.unlink()
                    except Exception:
                        open(self.sent_list_file, "w", encoding="utf-8").close()
            except Exception as e:
                messagebox.showerror(APP_NAME, f"Не удалось очистить список: {e}")
                return
        self.append_log("[АНТИДУБЛЬ] Список отправленных e-mail очищен.")
        self.status_var.set("Список отправленных e-mail очищен")

    # --- Команды UI ---
    def show_about(self):
        messagebox.showinfo(
            APP_NAME,
            "Разработка: IT_Team\n\n"
            "2025\n"
            "Лицензия предоставлена покупателю Kwork user_20830553"
        )

    def append_log(self, msg: str):
        self.queue.put(msg)

    def _drain_queue(self):
        try:
            while True:
                msg = self.queue.get_nowait()
                self.log.configure(state="normal")
                self.log.insert("end", msg + "\n")
                self.log.see("end")
                self.log.configure(state="disabled")
        except queue.Empty:
            pass
        self.after(150, self._drain_queue)

    def on_close(self):
        if self.scheduler_thread and self.scheduler_thread.is_alive():
            self.scheduler_stop_event.set()
        if any(t.is_alive() for t in self.sending_threads_multi):
            if not messagebox.askyesno(APP_NAME, "Идёт отправка. Остановить и выйти?"):
                return
            self.stop_event.set()
            self.after(100, self._await_thread_stop_and_close)
            return
        self.save_config()
        self.destroy()

    def _await_thread_stop_and_close(self):
        still = any(t.is_alive() for t in self.sending_threads_multi)
        if still:
            self.after(150, self._await_thread_stop_and_close)
        else:
            self.save_config()
            self.destroy()

    # --- Конфиг ---
    def save_config(self):
        try:
            data = dict(
                smtp_accounts_text=self.smtp_accounts_text.get(),

                def_start_row=int(self.def_start_row.get()),
                def_email_col=int(self.def_email_col.get()),
                def_fio_from=int(self.def_fio_from.get()),
                def_fio_to=int(self.def_fio_to.get()),

                limit_count=int(self.limit_count.get()),
                delay_sec=int(self.delay_sec.get()),
                pair_mode=bool(self.pair_mode.get()),

                random_limit_enabled=bool(self.random_limit_enabled.get()),
                limit_min=int(self.limit_min.get()),
                limit_max=int(self.limit_max.get()),

                random_delay_enabled=bool(self.random_delay_enabled.get()),
                delay_min=int(self.delay_min.get()),
                delay_max=int(self.delay_max.get()),

                schedule_enabled=bool(self.schedule_enabled.get()),
                schedule_days={str(k): bool(v.get()) for k, v in self.schedule_days_vars.items()},
                schedule_times={str(k): self.schedule_times[k].get() for k in self.schedule_times},

                rand_time_enabled=bool(self.rand_time_enabled.get()),
                rand_time_min=int(self.rand_time_min.get()),
                rand_time_max=int(self.rand_time_max.get()),

                subject_tpl=self.subject_tpl.get(),
                body_tpl=self.body_tpl.get(),
                subject_tpl_nofio=self.subject_tpl_nofio.get(),
                body_tpl_nofio=self.body_tpl_nofio.get(),
                campaign_theme=self.campaign_theme.get(),
                campaign_wishes=self._get_campaign_wishes(),
                mailing_id=self.mailing_id.get(),

                attachments=self.attachments,
                attachments_description=self.attachments_description.get(),
                company_site=self.company_site.get(),
            )
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            self.status_var.set(f"Настройки сохранены: {CONFIG_FILE.name}")
        except Exception as e:
            messagebox.showerror(APP_NAME, f"Ошибка сохранения настроек: {e}")

    def load_config(self):
        if not CONFIG_FILE.exists():
            self._refresh_sources_listbox()
            return
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)

            self.smtp_accounts_text.set(data.get("smtp_accounts_text", self.smtp_accounts_text.get()))
            if hasattr(self, "smtp_accounts_box"):
                self.after(0, lambda: (self.smtp_accounts_box.delete("1.0","end"),
                                       self.smtp_accounts_box.insert("1.0", self.smtp_accounts_text.get())))

            self.def_start_row.set(int(data.get("def_start_row", self.def_start_row.get())))
            self.def_email_col.set(int(data.get("def_email_col", self.def_email_col.get())))
            self.def_fio_from.set(int(data.get("def_fio_from", self.def_fio_from.get())))
            self.def_fio_to.set(int(data.get("def_fio_to", self.def_fio_to.get())))

            self.limit_count.set(int(data.get("limit_count", self.limit_count.get())))
            self.delay_sec.set(int(data.get("delay_sec", self.delay_sec.get())))
            self.pair_mode.set(bool(data.get("pair_mode", self.pair_mode.get())))

            self.random_limit_enabled.set(bool(data.get("random_limit_enabled", self.random_limit_enabled.get())))
            self.limit_min.set(int(data.get("limit_min", self.limit_min.get())))
            self.limit_max.set(int(data.get("limit_max", self.limit_max.get())))

            self.random_delay_enabled.set(bool(data.get("random_delay_enabled", self.random_delay_enabled.get())))
            self.delay_min.set(int(data.get("delay_min", self.delay_min.get())))
            self.delay_max.set(int(data.get("delay_max", self.delay_max.get())))

            self.schedule_enabled.set(bool(data.get("schedule_enabled", self.schedule_enabled.get())))
            sd = data.get("schedule_days", {})
            for k, var in self.schedule_days_vars.items():
                var.set(bool(sd.get(str(k), var.get())))
            st = data.get("schedule_times", {})
            for k in self.schedule_times:
                self.schedule_times[k].set(st.get(str(k), self.schedule_times[k].get()))

            self.rand_time_enabled.set(bool(data.get("rand_time_enabled", self.rand_time_enabled.get())))
            self.rand_time_min.set(int(data.get("rand_time_min", self.rand_time_min.get())))
            self.rand_time_max.set(int(data.get("rand_time_max", self.rand_time_max.get())))

            self.subject_tpl.set(data.get("subject_tpl", self.subject_tpl.get()))
            self.body_tpl.set(data.get("body_tpl", self.body_tpl.get()))

            self.subject_tpl_nofio.set(data.get("subject_tpl_nofio", self.subject_tpl_nofio.get()))
            self.body_tpl_nofio.set(data.get("body_tpl_nofio", self.body_tpl_nofio.get()))
            self.campaign_theme.set(data.get("campaign_theme", self.campaign_theme.get()))
            self._set_campaign_wishes_text(data.get("campaign_wishes", self._campaign_wishes_value))

            self.attachments = list(data.get("attachments", []))
            if hasattr(self, "attach_list"):
                self.attach_list.delete(0, "end")
                for p in self.attachments:
                    self.attach_list.insert("end", p)

            self.mailing_id.set(data.get("mailing_id", self.mailing_id.get()))

            self.attachments_description.set(data.get("attachments_description", self.attachments_description.get()))
            self.company_site.set(data.get("company_site", self.company_site.get()))

            self._update_controls_state()
            self._ensure_scheduler_running()
            self.status_var.set(f"Настройки загружены: {CONFIG_FILE.name}")
        except Exception as e:
            messagebox.showerror(APP_NAME, f"Ошибка загрузки настроек: {e}")

    def _update_controls_state(self):
        state_rand_lim = "normal" if self.random_limit_enabled.get() else "disabled"
        self.spin_lmin.configure(state=state_rand_lim)
        self.spin_lmax.configure(state=state_rand_lim)
        self.spin_limit.configure(state="disabled" if self.random_limit_enabled.get() else "normal")

        state_rand_del = "normal" if self.random_delay_enabled.get() else "disabled"
        self.spin_delay_min.configure(state=state_rand_del)
        self.spin_delay_max.configure(state=state_rand_del)
        self.spin_delay.configure(state="disabled" if self.random_delay_enabled.get() else "normal")

    # --- Валидация ---
    def _validate_settings(self) -> Optional[str]:
        accs = self._get_accounts()
        if not accs:
            return "Не заданы SMTP-аккаунты (введите хотя бы одну строку)."

        if not self.mailing_id.get().strip():
            return "Введите ID рассылки (поле под шаблонами писем)."

        bad = []
        for a in accs:
            if a.src_id is None:
                bad.append(f"{a.login}: не указан src=ID")
            else:
                src = self._get_source_by_id(a.src_id)
                if not (src and Path(src.get('path', '')).exists()):
                    bad.append(f"{a.login}: src={a.src_id} не найден в пуле или файл отсутствует")

        if bad:
            return ("Для каждого аккаунта должен быть выбран источник (src=ID) с существующим файлом.\n" +
                    "\n".join(" - " + x for x in bad))

        if self.random_limit_enabled.get():
            if int(self.limit_min.get()) < 1 or int(self.limit_max.get()) < int(self.limit_min.get()):
                return "Задайте корректный интервал случайного дневного лимита."
        else:
            if int(self.limit_count.get()) < 1:
                return "Лимит писем должен быть ≥ 1."
        if self.random_delay_enabled.get():
            if int(self.delay_min.get()) < 0 or int(self.delay_max.get()) < int(self.delay_min.get()):
                return "Задайте корректный интервал случайной задержки."
        else:
            if int(self.delay_sec.get()) < 0:
                return "Задержка не может быть отрицательной."
        return None

    # --- Доступ к данным строки ---
    @staticmethod
    def _pick_emails_from_row_with_cols(row: pd.Series, email_col: int) -> List[str]:
        idx = int(email_col) - 1
        try:
            cell = row.iloc[idx]
        except IndexError:
            return []
        return extract_emails(cell)

    @staticmethod
    def _pick_fio_best_from_row_with_cols(row: pd.Series, fio_from: int, fio_to: int) -> Tuple[str, float, str]:
        best = ("", -1.0, "")
        start = int(fio_from) - 1
        end = int(fio_to) - 1
        for col in range(start, end + 1):
            try:
                value = row.iloc[col]
            except IndexError:
                break
            if pd.isna(value):
                continue
            text = str(value)
            fio = extract_fio(text)
            if fio:
                score = 1.0
                if fio.split()[0].lower() in COMMON_RU_NAMES:
                    score += 1.0
                if _contains_stop_context(text):
                    score -= 1.0
                if score > best[1]:
                    best = (fio, score, text[:160])
        return best

    @staticmethod
    def _extract_name_list_from_row_with_cols(row: pd.Series, fio_from: int, fio_to: int) -> List[str]:
        names: List[str] = []
        start = int(fio_from) - 1
        end = int(fio_to) - 1
        for col in range(start, end + 1):
            try:
                value = row.iloc[col]
            except IndexError:
                break
            if pd.isna(value):
                continue
            cell = str(value)
            chunks = re.split(r"[;,/|]\s*|\n+", cell)
            for ch in chunks:
                fio = extract_fio(ch)
                if fio:
                    names.append(fio)
        seen = set()
        uniq = []
        for n in names:
            key = n.lower()
            if key not in seen:
                seen.add(key)
                uniq.append(n)
        return uniq

    # --- Тестовый предпросмотр ---
    def compose_test_email(self):
        fio = self.preview_fio
        to_email = (self.preview_target_email.get() or "").strip() or "demo@example.com"
        self.active_campaign_theme = self.campaign_theme.get().strip()
        self.active_campaign_wishes = self._get_campaign_wishes()
        self.active_subject_tpl = self.subject_tpl.get()
        self._set_preview_text("Формирую тестовое письмо…")
        if hasattr(self, "btn_compose_preview"):
            try:
                self.btn_compose_preview.configure(state="disabled", text="Генерация…")
            except Exception:
                pass
        threading.Thread(target=self._compose_test_worker, args=(fio, to_email), daemon=True).start()

    def _compose_test_worker(self, fio: str, to_email: str):
        try:
            subj, plain, html_fallback = self._render_named(fio, to_email)
            llm_html, llm_plain = self._generate_llm_email(fio, to_email)
            if llm_html:
                body_plain = llm_plain or plain
                body_html = llm_html
                source_hint = "LLM + шаблон"
            else:
                body_plain = plain
                body_html = html_fallback
                source_hint = "Шаблон"

            html_for_render = body_html or f"<pre>{html.escape(body_plain or '').strip()}</pre>"
            lines = [
                f"Тестовое ФИО: {fio}",
                f"Получатель: {to_email}",
                f"Источник текста: {source_hint}",
                f"Тема: {subj}",
                "",
                "Текст письма:",
                (body_plain or "").strip() or "(пусто)",
            ]
            if body_html:
                lines.extend(["", "HTML-версия:", body_html.strip()])
            preview_text = "\n".join(lines)
            self.after(0, lambda: self._finish_preview(preview_text, html_for_render))
        except Exception as e:
            self.append_log(f"[PREVIEW] Ошибка генерации: {e}")
            self.after(0, lambda: self._finish_preview(f"Не удалось составить тестовое письмо: {e}", None))

    def _finish_preview(self, text: str, html_content: Optional[str]):
        self._set_preview_text(text)
        self._render_html_preview(html_content)
        if hasattr(self, "btn_compose_preview"):
            try:
                self.btn_compose_preview.configure(state="normal", text="Составить тестовое письмо")
            except Exception:
                pass

    # --- Тестовая отправка: со всех аккаунтов ---
    def _send_test_all_worker(self, to_email: str):
        fio_demo = "Мария Петровна"
        subj, body, body_html = self._render_named(fio_demo, to_email)
        llm_html, llm_plain = self._generate_llm_email(fio_demo, to_email)
        if llm_html:
            body = llm_plain or body
            body_html = llm_html
        accs = self._get_accounts()
        ok = 0
        for acc in accs[:10]:
            sender = SMTPSender(acc.host, acc.port, acc.security, acc.login, acc.password, acc.from_name)
            try:
                sender.connect()
                sender.send(to_email, f"[TEST] {subj} (от {acc.login})", body,
                            attachments=self.attachments, body_html=body_html)
                ok += 1
                self.append_log(f"[TEST] Отправлено от {acc.login} → {to_email}")
            except Exception as e:
                self.append_log(f"[TEST][ОШИБКА] {acc.login}: {e}")
            finally:
                sender.close()
        self.after(0, lambda: (
            self._set_buttons_state(False),
            messagebox.showinfo(APP_NAME, f"Тестовая отправка завершена. Успешно: {ok}/{min(len(accs),10)}.")
        ))

    def send_test_all(self):
        accs = self._get_accounts()
        if not accs:
            messagebox.showwarning(APP_NAME, "Добавьте хотя бы один SMTP-аккаунт.")
            return
        to = simpledialog.askstring(APP_NAME, "Куда отправить тест? Укажите e-mail:")
        if not to:
            return
        self._set_buttons_state(True)
        threading.Thread(target=self._send_test_all_worker, args=(to,), daemon=True).start()

    # --- Старт/Стоп ---
    def start_sending(self):
        err = self._validate_settings()
        if err:
            messagebox.showwarning(APP_NAME, err)
            return
        if any(t.is_alive() for t in self.sending_threads_multi):
            self.status_var.set("Идёт рассылка/остановка, подождите…")
            return

        self.stop_event.clear()
        topic = self.campaign_theme.get().strip()
        wishes = self._get_campaign_wishes()
        self.active_attachments_description = self.attachments_description.get().strip()
        self.active_campaign_theme = topic
        self.active_campaign_wishes = wishes
        self.active_subject_tpl = self.subject_tpl.get()
        if topic or wishes:
            brief = (wishes[:80] + "…") if len(wishes) > 80 else wishes
            self.append_log(f"[РАССЫЛКА] Тема генерации: {topic or '-'} | пожелания: {brief or '-'}")
        self.active_mailing_id = self.mailing_id.get().strip()
        self.sending_threads_multi.clear()

        accounts = self._get_accounts()
        if self.sending_thread_single and self.sending_thread_single.is_alive():
            self.status_var.set("Уже идёт рассылка, подождите…")
            return
        t = threading.Thread(target=self._send_all_round_robin, args=(accounts[:10],), daemon=True)
        t.start()
        self.sending_threads_multi = [t]
        self.sending_thread_single = t

        self._set_buttons_state(True)

    def stop_sending(self):
        if any(t.is_alive() for t in self.sending_threads_multi):
            self.stop_event.set()
            self.append_log("[СТОП] Остановка запрошена пользователем.")
            self.status_var.set("Останавливаю рассылку…")
            self.after(150, self._await_thread_stop)
        else:
            self.status_var.set("Рассылка не запущена.")

    def _await_thread_stop(self):
        still = [t for t in self.sending_threads_multi if t.is_alive()]
        if still:
            self.after(150, self._await_thread_stop)
        else:
            self.sending_threads_multi.clear()
            self._set_buttons_state(False)
            self.status_var.set("Остановлено.")

    # --- Рендер шаблонов ---
    def _render_named(self, fio: str, to: str) -> Tuple[str, str, Optional[str]]:
        subj = self.subject_tpl.get()
        body_tpl = self.body_tpl.get()
        try:
            body_formatted = body_tpl.format(fio=fio, email=to)
            subj = subj.format(fio=fio, email=to)
        except Exception:
            body_formatted = body_tpl.replace("{fio}", fio).replace("{email}", to)
            subj = subj.replace("{fio}", fio).replace("{email}", to)

        return subj, body_formatted, None

    def _render_nofio(self, to: str) -> Tuple[str, str, Optional[str]]:
        subj = self.subject_tpl_nofio.get()
        body_tpl = self.body_tpl_nofio.get()
        try:
            body_formatted = body_tpl.format(email=to, fio="")
            subj = subj.format(email=to, fio="")
        except Exception:
            body_formatted = body_tpl.replace("{email}", to).replace("{fio}", "")
            subj = subj.replace("{email}", to).replace("{fio}", "")

        return subj, body_formatted, None

    def _choose_limit_for_session(self) -> int:
        if self.random_limit_enabled.get():
            a, b = int(self.limit_min.get()), int(self.limit_max.get())
            if b < a:
                a, b = b, a
            val = random.randint(a, b)
            self.append_log(f"[ЛИМИТ] Случайный дневной лимит выбран: {val} (интервал {a}-{b})")
            return val
        else:
            return int(self.limit_count.get())

    def _choose_delay_for_next(self) -> int:
        if self.random_delay_enabled.get():
            a, b = int(self.delay_min.get()), int(self.delay_max.get())
            if b < a:
                a, b = b, a
            return random.randint(a, b)
        else:
            return int(self.delay_sec.get())

    # --- Вспомогательное: источник по ID ---
    def _get_source_by_id(self, src_id: int) -> Optional[Dict[str, Any]]:
        try:
            rows = self._db_fetchall(
                "SELECT id, path, start_row, email_col, fio_from, fio_to FROM source_file WHERE id=? LIMIT 1",
                (int(src_id),)
            )
            if not rows:
                return None
            r = rows[0]
            return dict(id=r[0], path=r[1], start_row=int(r[2]), email_col=int(r[3]), fio_from=int(r[4]), fio_to=int(r[5]))
        except Exception:
            return None

    # --- Воркер на аккаунт ---
    def _collect_tasks_for_account(self, account: SMTPAccount) -> Optional[Dict[str, Any]]:
        self.append_log(f"[АККАУНТ] Старт: {account.login} (src={'-' if account.src_id is None else account.src_id})")
        src_info = self._get_source_by_id(account.src_id) if account.src_id is not None else None
        if not src_info or not Path(src_info.get("path", "")).exists():
            self.append_log(f"[{account.login}] [ОТМЕНА] Для аккаунта не выбран валидный источник (src=ID) или файл отсутствует.")
            return None

        use_path = src_info["path"]
        use_start = int(src_info.get("start_row", 1))
        use_email_col = int(src_info.get("email_col", 1))
        use_fio_from = int(src_info.get("fio_from", 1))
        use_fio_to = int(src_info.get("fio_to", use_fio_from))

        contacts_cache = self._list_contacts(account.src_id) if account.src_id is not None else []

        df = None
        if not contacts_cache:
            try:
                df = read_table(use_path, start_row=use_start)
            except Exception as e:
                self.append_log(f"[{account.login}] [ОШИБКА] Чтение файла: {e}")
                return None

        tasks: List[Dict[str, Any]] = []
        if contacts_cache:
            for idx, row in enumerate(contacts_cache, start=1):
                email = row.get("email") if isinstance(row, dict) else row[1]
                fio_val = (row.get("fio") if isinstance(row, dict) else "") or ""
                tasks.append(dict(idx=idx, email=email, fio=fio_val, fio_score=1.0,
                                  fio_src="contacts", used_pair=False, from_db=True))
        else:
            for idx, row in df.iterrows():  # type: ignore
                emails = self._pick_emails_from_row_with_cols(row, use_email_col)
                if not emails:
                    continue
                best_fio, fio_score, fio_src = self._pick_fio_best_from_row_with_cols(row, use_fio_from, use_fio_to)
                name_list = self._extract_name_list_from_row_with_cols(row, use_fio_from, use_fio_to) if self.pair_mode.get() else []
                for i, to in enumerate(emails):
                    fio_to_use = ""
                    used_pair = False
                    if self.pair_mode.get() and i < len(name_list):
                        fio_to_use = name_list[i]; used_pair = True
                    elif best_fio:
                        fio_to_use = best_fio
                    tasks.append(dict(
                        idx=idx+1,
                        email=to,
                        fio=fio_to_use,
                        fio_score=fio_score,
                        fio_src=fio_src,
                        used_pair=used_pair,
                        from_db=False,
                    ))

        limit = self._choose_limit_for_session()
        src_tag = f'ID {account.src_id}'
        total_rows = len(contacts_cache) if contacts_cache else (len(df) if df is not None else 0)
        self.append_log(f"[{account.login}] Источник: {src_tag} → {Path(use_path).name}; колонки: email={use_email_col}, fio={use_fio_from}-{use_fio_to}; старт={use_start}")
        self.append_log(f"[{account.login}] План: {limit} писем. Вложений: {len(self.attachments)}")

        try:
            sender = SMTPSender(account.host, account.port, account.security,
                                account.login, account.password, account.from_name)
            sender.connect()
        except Exception as e:
            self.append_log(f"[{account.login}] [ОШИБКА] SMTP подключение: {e}")
            return None

        return dict(
            account=account,
            tasks=tasks,
            sender=sender,
            limit=limit,
            sent=0,
            new_pairs=[],
            total_rows=total_rows,
        )

    def _send_single_email(self, state: Dict[str, Any], task: Dict[str, Any]):
        account: SMTPAccount = state["account"]
        sender: SMTPSender = state["sender"]
        to = task["email"]
        fio_to_use = task.get("fio") or ""
        used_pair = bool(task.get("used_pair"))
        fio_score = float(task.get("fio_score", 1.0))
        fio_src = task.get("fio_src", "")
        from_db = bool(task.get("from_db"))
        idx = task.get("idx", 0)
        try:
            sender.ensure_connected()
            if fio_to_use:
                subj, fallback_plain, fallback_html = self._render_named(fio_to_use, to)
            else:
                subj, fallback_plain, fallback_html = self._render_nofio(to)

            llm_html, llm_plain = self._generate_llm_email(fio_to_use, to)
            if llm_html:
                body = llm_plain or fallback_plain
                body_html = llm_html
            else:
                body = fallback_plain
                body_html = fallback_html

            sender.send(to, subj, body, attachments=self.attachments, body_html=body_html)
            state["sent"] += 1
            if not from_db:
                state["new_pairs"].append((to, fio_to_use))
            if fio_to_use:
                tag = "(pair)" if used_pair else f"(score={fio_score:.2f})"
                self.append_log(f"[{account.login}] [OK] → {to} | «{subj}» | FIO='{fio_to_use}' {tag} | влож.: {len(self.attachments)}")
                if not used_pair and fio_score < 0.5 and fio_src:
                    self.append_log(f"[{account.login}] [ВНИМАНИЕ] Низкая уверенность: '{fio_to_use}'. Источник-ячейка: {fio_src}")
            else:
                self.append_log(f"[{account.login}] [OK] → {to} | «{subj}» | без ФИО | влож.: {len(self.attachments)}")

            self._add_sent_email(to)
            self._log_sent_email_db(to, fio_to_use)
            self.status_var.set(f"{account.login}: {state['sent']}/{state['limit']} | строка {idx}/{state.get('total_rows', 0)}")
        except Exception as e:
            self.append_log(f"[{account.login}] [ОШИБКА] {to}: {e}")

    def _send_all_round_robin(self, accounts: List[SMTPAccount]):
        states: List[Dict[str, Any]] = []
        for acc in accounts:
            st = self._collect_tasks_for_account(acc)
            if st:
                states.append(st)
        if not states:
            self.after(0, lambda: self._set_buttons_state(False))
            return

        try:
            while not self.stop_event.is_set():
                active = False
                for st in states:
                    if st["sent"] >= st["limit"]:
                        continue
                    if not st["tasks"]:
                        continue
                    active = True
                    task = st["tasks"].pop(0)
                    key = (task.get("email") or "").strip().lower()
                    if key in self.sent_emails:
                        self.append_log(f"[{st['account'].login}] [СКИП] Уже отправляли → {task.get('email')}")
                        continue
                    self._send_single_email(st, task)
                    if self.stop_event.is_set():
                        break
                    if st["sent"] < st["limit"]:
                        delay = self._choose_delay_for_next()
                        if delay > 0 and (not self.stop_event.is_set()):
                            time.sleep(delay)
                if not active:
                    break
            for st in states:
                if st.get("new_pairs"):
                    self._remember_contacts(st["account"].src_id, st["new_pairs"])
                self.append_log(f"[{st['account'].login}] Готово. Отправлено: {st['sent']}/{st['limit']}.")
        finally:
            for st in states:
                try:
                    sender = st.get("sender")
                    if sender:
                        sender.close()
                except Exception:
                    pass
            self.after(0, lambda: self._set_buttons_state(False))

    def _set_buttons_state(self, sending: bool):
        if hasattr(self, "btn_start"):
            self.btn_start.configure(state="disabled" if sending else "normal")
        if hasattr(self, "btn_stop"):
            self.btn_stop.configure(state="normal" if sending else "disabled")

    # --- Планировщик ---
    def _wire_schedule_toggle(self):
        self.schedule_enabled.trace_add("write", lambda *args: (self._toggle_scheduler(), self._set_schedule_controls_state()))

    def _set_schedule_controls_state(self):
        state = "normal"
        for w in getattr(self, "_schedule_controls", []):
            try:
                w.configure(state=state)
            except Exception:
                pass

    def _toggle_scheduler(self):
        self.save_config()
        self._ensure_scheduler_running()

    def _ensure_scheduler_running(self):
        enabled = self.schedule_enabled.get()
        if enabled:
            if not (self.scheduler_thread and self.scheduler_thread.is_alive()):
                self.scheduler_stop_event.clear()
                self.scheduler_thread = threading.Thread(target=self._scheduler_worker, daemon=True)
                self.scheduler_thread.start()
                self.append_log("[РАСПИСАНИЕ] Планировщик запущен.")
        else:
            if self.scheduler_thread and self.scheduler_thread.is_alive():
                self.scheduler_stop_event.set()
                self.append_log("[РАСПИСАНИЕ] Планировщик остановлен.")

    def _parse_schedule_times(self) -> dict:
        out = {}
        for d in range(7):
            t = self.schedule_times[d].get().strip()
            try:
                dt = datetime.strptime(t, "%H:%M")
                out[d] = (dt.hour, dt.minute)
            except Exception:
                self.append_log(f"[РАСПИСАНИЕ] Неверное время '{t}' для дня {d}, используем 10:30.")
                out[d] = (10, 30)
        return out

    def _scheduler_worker(self):
        while not self.scheduler_stop_event.is_set():
            try:
                if not self.schedule_enabled.get():
                    time.sleep(1.0)
                    continue

                now = datetime.now()
                weekday = now.weekday()
                if not self.schedule_days_vars.get(weekday, tk.BooleanVar(value=False)).get():
                    time.sleep(10.0)
                    continue

                hhmm = self._parse_schedule_times().get(weekday, (10, 30))
                base_dt = now.replace(hour=hhmm[0], minute=hhmm[1], second=0, microsecond=0)

                if self.rand_time_enabled.get():
                    a, b = int(self.rand_time_min.get()), int(self.rand_time_max.get())
                    if b < a:
                        a, b = b, a
                    sign = 1 if random.random() < 0.5 else -1
                    shift = sign * random.randint(a, b)
                    base_dt = base_dt + timedelta(minutes=shift)

                today_key = now.strftime("%Y-%m-%d")
                if self.last_run_date == today_key:
                    time.sleep(15.0)
                    continue

                if now >= base_dt:
                    if not any(t.is_alive() for t in self.sending_threads_multi):
                        self.append_log(f"[РАСПИСАНИЕ] Старт {today_key} запланировано на {base_dt.strftime('%H:%M')}")
                        self.last_run_date = today_key
                        self.after(0, self.start_sending)
                    else:
                        self.append_log("[РАСПИСАНИЕ] Пропуск: уже идёт отправка.")
                    time.sleep(30.0)
                else:
                    secs = int((base_dt - now).total_seconds())
                    self.status_var.set(f"Следующий запуск ~{secs//60} мин (цель: {base_dt.strftime('%H:%M')})")
                    time.sleep(10.0)
            except Exception as e:
                self.append_log(f"[РАСПИСАНИЕ] Ошибка: {e}")
                time.sleep(5.0)

    # --- Мультиаккаунты ---
    def _get_accounts(self) -> List[SMTPAccount]:
        accounts: List[SMTPAccount] = []
        for rec in self._list_smtp_accounts():
            try:
                port = int(rec["port"])
            except Exception:
                self.append_log(f"[АККАУНТЫ] Неверный порт для {rec['email']}")
                continue
            sec = rec.get("security", "SSL")
            if sec not in ("SSL", "STARTTLS", "PLAIN"):
                self.append_log(f"[АККАУНТЫ] Неверная защита: {sec} для {rec['email']}")
                continue
            accounts.append(
                SMTPAccount(
                    host=rec["host"],
                    port=port,
                    security=sec,
                    login=rec["email"],
                    password=rec.get("password", ""),
                    from_name=rec.get("from_name", ""),
                    src_id=rec.get("source_id"),
                )
            )
        return accounts

# ==========================
# Точка входа
# ==========================
def main():
    app = App()
    app.protocol("WM_DELETE_WINDOW", app.on_close)
    app.mainloop()

if __name__ == "__main__":
    main()
