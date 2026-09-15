#!/usr/bin/env python3
"""
Voice2Lecture — офлайн-превращение аудио и голосовых в конспект.
Без интернета, без API-ключей, без подписок.
"""

import os
import re
import sys
import json
import queue
import shutil
import wave
import threading
import subprocess
import tempfile
from pathlib import Path
from datetime import datetime
from collections import Counter

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext

# ---------- опциональные зависимости ----------
try:
    from vosk import Model, KaldiRecognizer, SetLogLevel
    HAS_VOSK = True
    SetLogLevel(-1)
except ImportError:
    HAS_VOSK = False

try:
    import sounddevice as sd
    import numpy as np
    HAS_SD = True
except ImportError:
    HAS_SD = False

try:
    import soundfile as sf
    HAS_SF = True
except ImportError:
    HAS_SF = False

APP_DIR = Path(__file__).parent
MODELS_DIR = APP_DIR / "models"
SAMPLE_RATE = 16000

# ---------- стоп-слова ----------
STOPWORDS = set("""
а без более бы был была были было быть в вам вас вдруг ведь во вот впрочем все всего всех вы
где да даже два для до другой его ее ей ему если есть еще ж же за здесь и из или им иногда их
к как какая какой когда конечно кто куда ли лучше между меня мне много можно мой моя мы на над
надо наконец нас не него нее ней нельзя нет ни нибудь никогда ним них ничего но ну о об один он
она они опять от перед по под после потом почти при про раз разве с сам свою себе себя
сейчас со совсем так такой там тебя тем теперь то тогда того тоже той только том тот тут ты у
уж уже хорошо хоть чего чем через что чтоб чтобы чуть эти этого этой этом этот эту я
the a an and or but is are was were be been being in on at to from for of with by this that
these those it its as if then than so we you they he she i me my your our their
""".split())


# ---------- конвертация аудио ----------
def convert_to_wav(src: str) -> str:
    """Любой аудиофайл -> 16 kHz mono WAV."""
    tmp = tempfile.NamedTemporaryFile(suffix=".wav", delete=False)
    dst = tmp.name
    tmp.close()

    ffmpeg = shutil.which("ffmpeg")
    if ffmpeg:
        cmd = [ffmpeg, "-y", "-i", src, "-ar", str(SAMPLE_RATE),
               "-ac", "1", "-f", "wav", "-acodec", "pcm_s16le", dst]
        r = subprocess.run(cmd, capture_output=True)
        if r.returncode == 0 and os.path.getsize(dst) > 44:
            return dst
        try: os.remove(dst)
        except OSError: pass

    if HAS_SF and HAS_SD:
        data, sr = sf.read(src, dtype="float32")
        if data.ndim > 1:
            data = data.mean(axis=1)
        if sr != SAMPLE_RATE:
            new_len = int(len(data) * SAMPLE_RATE / sr)
            idx = np.linspace(0, len(data) - 1, new_len)
            data = np.interp(idx, np.arange(len(data)), data)
        data16 = (data * 32767).astype("int16")
        sf.write(dst, data16, SAMPLE_RATE, subtype="PCM_16")
        return dst

    raise RuntimeError(
        "Не могу сконвертировать файл.\n"
        "Установите ffmpeg или выполните: pip install soundfile numpy sounddevice"
    )


# ---------- локальное структурирование (без ИИ) ----------
def clean_text(text: str) -> str:
    text = re.sub(r"\b(ну|вот|это|как\s+бы|типа|короче|значит|так\s+сказать)\b[,]?\s*",
                  "", text, flags=re.IGNORECASE)
    text = re.sub(r"\s+", " ", text)
    return text.strip()


def split_sentences(text: str):
    parts = re.split(r"(?<=[.!?…])\s+", text)
    return [p.strip() for p in parts if len(p.strip()) > 2]


def key_terms(text: str, top_n: int = 12):
    words = re.findall(r"[А-Яа-яЁёA-Za-z]{5,}", text.lower())
    freq = Counter(w for w in words if w not in STOPWORDS)
    return [w for w, c in freq.most_common(80) if c >= 2][:top_n]


def make_heading(sentence: str) -> str:
    s = sentence.rstrip(".!?…").strip()
    if len(s) > 68:
        s = s[:68]
        sp = s.rfind(" ")
        if sp > 30:
            s = s[:sp]
        s += "…"
    return (s[0].upper() + s[1:]) if s else "Блок"


def local_structure(text: str) -> str:
    text = clean_text(text)
    sentences = split_sentences(text)
    if not sentences:
        return "# Конспект\n\n_(текст пуст)_"

    blocks, cur, cur_len = [], [], 0
    for s in sentences:
        cur.append(s)
        cur_len += len(s)
        if len(cur) >= 5 or cur_len >= 600:
            blocks.append(cur)
            cur, cur_len = [], 0
    if cur:
        blocks.append(cur)

    terms = key_terms(text)
    words = len(text.split())

    out = []
    out.append("# Конспект лекции\n")
    out.append(f"_Слов: {words} · Предложений: {len(sentences)} · Блоков: {len(blocks)}_\n")

    out.append("## Кратко\n")
    for b in blocks[:6]:
        out.append(f"- {b[0]}")
    out.append("")

    if terms:
        out.append("## Ключевые термины\n")
        for t in terms:
            out.append(f"- **{t}**")
        out.append("")

    out.append("---\n")
    out.append("## Основная часть\n")
    for i, b in enumerate(blocks, 1):
        out.append(f"### {i}. {make_heading(b[0])}\n")
        for s in b:
            out.append(f"- {s}")
        out.append("")

    return "\n".join(out)


# ---------- приложение ----------
class Voice2Lecture(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Voice2Lecture — офлайн-конспект из аудио")
        self.geometry("1240x780")
        self.minsize(960, 620)

        self.model = None
        self.model_path = tk.StringVar()
        self.status = tk.StringVar(value="Готов")
        self.is_recording = False
        self.audio_queue = queue.Queue()

        self._build_ui()
        self._autodetect_model()
        self._check_deps()

    # ---------- UI ----------
    def _build_ui(self):
        top = ttk.Frame(self, padding=8)
        top.pack(fill="x")

        ttk.Label(top, text="Модель Vosk:").pack(side="left")
        ttk.Entry(top, textvariable=self.model_path, width=52).pack(side="left", padx=4)
        ttk.Button(top, text="Обзор…", command=self.choose_model).pack(side="left")
        ttk.Button(top, text="Загрузить", command=self.load_model).pack(side="left", padx=4)
        ttk.Button(top, text="Скачать модели…", command=self.open_models_page).pack(side="left", padx=8)

        main = ttk.PanedWindow(self, orient="horizontal")
        main.pack(fill="both", expand=True, padx=8, pady=4)

        # --- левая колонка: транскрипт ---
        left = ttk.Frame(main)
        main.add(left, weight=1)

        lf = ttk.LabelFrame(left, text="Транскрипт", padding=6)
        lf.pack(fill="both", expand=True)
        self.txt_transcript = scrolledtext.ScrolledText(
            lf, wrap="word", font=("Consolas", 10), undo=True)
        self.txt_transcript.pack(fill="both", expand=True)

        ctrl = ttk.Frame(left, padding=(0, 6))
        ctrl.pack(fill="x")
        self.btn_rec = ttk.Button(ctrl, text="● Записать", command=self.toggle_record)
        self.btn_rec.pack(side="left")
        ttk.Button(ctrl, text="📁 Открыть аудио",
                   command=self.open_audio).pack(side="left", padx=4)
        ttk.Button(ctrl, text="Очистить",
                   command=self.clear_all).pack(side="left", padx=4)

        # --- правая колонка: конспект ---
        right = ttk.Frame(main)
        main.add(right, weight=1)

        rf = ttk.LabelFrame(right, text="Конспект", padding=6)
        rf.pack(fill="both", expand=True)
        self.txt_lecture = scrolledtext.ScrolledText(
            rf, wrap="word", font=("Consolas", 10), undo=True)
        self.txt_lecture.pack(fill="both", expand=True)

        rctrl = ttk.Frame(right, padding=(0, 6))
        rctrl.pack(fill="x")
        ttk.Button(rctrl, text="⚙ Структурировать",
                   command=self.build_lecture).pack(side="left")
        ttk.Button(rctrl, text="💾 Сохранить .md",
                   command=self.save_lecture).pack(side="left", padx=4)
        ttk.Button(rctrl, text="📋 Копировать",
                   command=self.copy_lecture).pack(side="left")

        bar = ttk.Frame(self, relief="sunken")
        bar.pack(fill="x", side="bottom")
        ttk.Label(bar, textvariable=self.status, padding=4).pack(side="left")

    # ---------- модель ----------
    def _autodetect_model(self):
        if MODELS_DIR.exists():
            for p in sorted(MODELS_DIR.iterdir()):
                if p.is_dir():
                    self.model_path.set(str(p))
                    return

    def choose_model(self):
        p = filedialog.askdirectory(title="Папка с моделью Vosk")
        if p:
            self.model_path.set(p)
            self.load_model()

    def load_model(self):
        path = self.model_path.get().strip()
        if not path or not Path(path).exists():
            messagebox.showwarning("Модель", "Укажите папку с моделью Vosk.")
            return
        if not HAS_VOSK:
            messagebox.showerror("Vosk", "Установите: pip install vosk")
            return
        self.status.set("Загружаю модель…")
        self.update_idletasks()
        try:
            self.model = Model(path)
            self.status.set(f"Модель готова: {Path(path).name}")
        except Exception as e:
            messagebox.showerror("Ошибка", f"Не удалось загрузить модель:\n{e}")
            self.status.set("Ошибка загрузки модели")

    def open_models_page(self):
        import webbrowser
        webbrowser.open("https://alphacephei.com/vosk/models")

    def _check_deps(self):
        missing = []
        if not HAS_VOSK: missing.append("vosk")
        if not HAS_SD:   missing.append("sounddevice")
        if not HAS_SF:   missing.append("soundfile")
        if missing:
            self.status.set("Не хватает пакетов: " + ", ".join(missing) +
                            "  →  pip install " + " ".join(missing))

    # ---------- запись ----------
    def toggle_record(self):
        if self.is_recording:
            self.stop_record()
        else:
            self.start_record()

    def start_record(self):
        if not self.model:
            messagebox.showwarning("Модель", "Сначала загрузите модель Vosk.")
            return
        if not HAS_SD:
            messagebox.showerror("Микрофон", "Установите: pip install sounddevice")
            return
        self.is_recording = True
        self.btn_rec.config(text="■ Остановить")
        self.status.set("● Запись… Говорите")
        threading.Thread(target=self._record_loop, daemon=True).start()

    def _record_loop(self):
        try:
            rec = KaldiRecognizer(self.model, SAMPLE_RATE)
            q = self.audio_queue

            def cb(indata, frames, time_info, status):
                q.put(bytes(indata))

            with sd.RawInputStream(samplerate=SAMPLE_RATE, blocksize=8000,
                                   dtype="int16", channels=1, callback=cb):
                while self.is_recording:
                    try:
                        data = q.get(timeout=0.5)
                    except queue.Empty:
                        continue
                    if rec.AcceptWaveform(data):
                        t = json.loads(rec.Result()).get("text", "").strip()
                        if t:
                            self._post(self._append_line, t)

            t = json.loads(rec.FinalResult()).get("text", "").strip()
            if t:
                self._post(self._append_line, t)
        except Exception as e:
            self._post(messagebox.showerror, "Ошибка записи", str(e))
        finally:
            self._post(self._on_record_done)

    def stop_record(self):
        self.is_recording = False

    def _on_record_done(self):
        self.btn_rec.config(text="● Записать")
        self.status.set("Запись остановлена")

    # ---------- аудиофайл ----------
    def open_audio(self):
        if not self.model:
            messagebox.showwarning("Модель", "Сначала загрузите модель Vosk.")
            return
        path = filedialog.askopenfilename(
            title="Выберите аудиофайл",
            filetypes=[
                ("Аудио", "*.wav *.mp3 *.ogg *.flac *.m4a *.opus *.webm *.aac *.wma *.mp4"),
                ("Все файлы", "*.*"),
            ])
        if not path:
            return
        self.status.set(f"Обрабатываю {Path(path).name}…")
        threading.Thread(target=self._transcribe_file, args=(path,), daemon=True).start()

    def _transcribe_file(self, path):
        wav = None
        try:
            wav = convert_to_wav(path)
            self._post(self.status.set, "Распознаю…")
            rec = KaldiRecognizer(self.model, SAMPLE_RATE)
            with wave.open(wav, "rb") as wf:
                if wf.getnchannels() != 1 or wf.getsampwidth() != 2:
                    raise RuntimeError("Ожидается mono 16-bit WAV")
                while True:
                    data = wf.readframes(4000)
                    if not data:
                        break
                    if rec.AcceptWaveform(data):
                        t = json.loads(rec.Result()).get("text", "").strip()
                        if t:
                            self._post(self._append_line, t)
            t = json.loads(rec.FinalResult()).get("text", "").strip()
            if t:
                self._post(self._append_line, t)
            self._post(self.status.set, f"Готово: {Path(path).name}")
        except Exception as e:
            self._post(messagebox.showerror, "Ошибка", f"Не удалось распознать файл:\n{e}")
            self._post(self.status.set, "Ошибка распознавания")
        finally:
            if wav:
                try: os.remove(wav)
                except OSError: pass

    # ---------- UI-хелперы ----------
    def _post(self, fn, *args):
        self.after(0, lambda: fn(*args))

    def _append_line(self, text):
        self.txt_transcript.insert("end", text + "\n")
        self.txt_transcript.see("end")

    # ---------- конспект ----------
    def build_lecture(self):
        text = self.txt_transcript.get("1.0", "end").strip()
        if not text:
            messagebox.showinfo("Пусто", "Нет текста для структурирования.")
            return
        md = local_structure(text)
        self.txt_lecture.delete("1.0", "end")
        self.txt_lecture.insert("1.0", md)
        self.status.set("Конспект готов")

    def save_lecture(self):
        content = self.txt_lecture.get("1.0", "end").strip()
        if not content:
            messagebox.showinfo("Пусто", "Сначала создайте конспект.")
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".md",
            filetypes=[("Markdown", "*.md"), ("Текст", "*.txt")],
            initialfile=f"lecture-{datetime.now():%Y-%m-%d}.md",
        )
        if not path:
            return
        Path(path).write_text(content, encoding="utf-8")
        self.status.set(f"Сохранено: {path}")

    def copy_lecture(self):
        content = self.txt_lecture.get("1.0", "end").strip()
        if content:
            self.clipboard_clear()
            self.clipboard_append(content)
            self.status.set("Скопировано в буфер обмена")

    def clear_all(self):
        if self.is_recording:
            self.stop_record()
        if not messagebox.askyesno("Очистить", "Удалить транскрипт и конспект?"):
            return
        self.txt_transcript.delete("1.0", "end")
        self.txt_lecture.delete("1.0", "end")
        self.status.set("Очищено")


if __name__ == "__main__":
    if not HAS_VOSK:
        print("Пакет vosk не установлен. Выполните: pip install vosk")
    app = Voice2Lecture()
    app.mainloop()
