# NovaMail (курсовая работа)

![Python](https://img.shields.io/badge/Python-3.10%2B-blue)
![GUI](https://img.shields.io/badge/GUI-Tkinter-4c1)
![Status](https://img.shields.io/badge/Status-educational-informational)

**NovaMail** — учебное desktop‑приложение (GUI) для составления и отправки e‑mail через SMTP с поддержкой нескольких аккаунтов, шаблонов письма и загрузки контактов из Excel/CSV.

> ⚠️ Важно: используйте только для тестов/учебных целей и рассылок по **согласованной** базе (opt‑in). Не используйте для спама.

---

## Возможности

- GUI на **Tkinter**
- Несколько SMTP‑отправителей (переключение/хранение в локальной БД)
- Импорт контактов из **.xlsx/.csv** (настраиваемая строка старта и колонки)
- Авто‑извлечение имени/отчества из текста (Natasha)
- Шаблоны письма *с ФИО* и *без ФИО*
- Опциональная генерация текста письма через **локальный** LLM (Ollama) + HTML‑шаблон
- Логи отправок в **SQLite** и защита от повторной отправки одному адресу

---

## Быстрый старт

### 1) Установка

```bash
python -m venv .venv
# Windows:
.venv\Scripts\activate
# macOS/Linux:
source .venv/bin/activate

pip install -r requirements.txt
```

### 2) Запуск

```bash
python novamail_bot.py
```

---

## Ollama (опционально)

Приложение может обращаться к локальному Ollama по адресу `http://localhost:11434` и просить модель сгенерировать структуру письма (subject + блоки контента), после чего подставляет значения в HTML‑шаблон `template_llm_email.html`.

Если Ollama не запущен — приложение использует обычные текстовые шаблоны.

Переменные окружения (необязательно):

- `OLLAMA_URL` — URL сервера Ollama (по умолчанию `http://localhost:11434`)
- `OLLAMA_MODEL` — имя модели (по умолчанию `email-writer`)

---

## Данные и конфигурация

- **Локальная БД** (лог отправок и справочники): `sent_mail_log.sqlite3`
- **Защита от дублей**: `sent_emails.txt`
- **Локальная конфигурация**: `novamail_bot.json` (не коммитить в репозиторий)

> В репозитории лучше хранить только пример: `novamail_bot.sample.json`.

---

## Структура проекта

```
.
├─ novamail_bot.py
├─ template_llm_email.html
├─ novamail_bot.sample.json
├─ requirements.txt
├─ .gitignore
└─ LICENSE
```

---


## Лицензия

MIT (см. файл `LICENSE`).

