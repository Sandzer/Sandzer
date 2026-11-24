#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AudioTagAI v5 Premium — Automatyczny tagger polskich audiobooków i muzyki
Źródła: Lubimyczytac.pl · Audioteka · Google Books PL · Open Library · Empik · iTunes
Uruchom: python AudioTagAI.py
"""

APP_VERSION = "5.0 Premium"

# ═══════════════════════════════════════════════════════════════════════════
#  AUTO-INSTALL — przy pierwszym uruchomieniu sam instaluje brakujące pakiety
# ═══════════════════════════════════════════════════════════════════════════
import sys, subprocess

def _ensure(pkg, import_as=None):
    try:
        __import__(import_as or pkg)
    except ImportError:
        print(f"[AudioTagAI] Instaluję {pkg}…")
        subprocess.check_call(
            [sys.executable, "-m", "pip", "install", pkg, "-q"],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL
        )

_ensure("mutagen")
_ensure("Pillow", "PIL")

# ═══════════════════════════════════════════════════════════════════════════

import os, re, json, math, time, base64, difflib, queue, threading, urllib.request, urllib.parse, html as html_mod
import logging, traceback
from logging.handlers import RotatingFileHandler
from pathlib import Path
from io import BytesIO
from typing import Optional

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import tkinter.font as tkfont
from PIL import Image, ImageTk, ImageDraw, ImageFilter, ImageOps

import mutagen
from mutagen.id3 import (ID3, ID3NoHeaderError,
    TIT2, TPE1, TPE2, TALB, TDRC, TCON, TRCK, TCOM, APIC, COMM)
from mutagen.flac import FLAC, Picture
from mutagen.mp4  import MP4, MP4Cover
try:
    from mutagen.oggvorbis import OggVorbis
    _OGG = True
except ImportError:
    _OGG = False

# ─── Kolory ───────────────────────────────────────────────────────────────
BG     = "#0e0f14"
PANEL  = "#161820"
CARD   = "#1e2133"
ACC    = "#7c6af7"
ACC2   = "#5eead4"
GREEN  = "#4ade80"
RED    = "#f87171"
AMBER  = "#fbbf24"
TEXT   = "#e2e8f0"
MUTED  = "#64748b"
BORDER = "#2a2d45"

AUDIO_EXT = {'.mp3', '.flac', '.m4a', '.aac', '.ogg', '.opus', '.wma'}
TAGGABLE_EXT = {'.mp3', '.flac', '.m4a', '.aac', '.ogg'}  # formaty do których faktycznie zapisujemy tagi

PL_UPPER = "A-ZĄĆĘŁŃÓŚŹŻ"
PL_WORD  = r"[A-ZĄĆĘŁŃÓŚŹŻa-ząćęłńóśźż\.\-']+"

# ═══════════════════════════════════════════════════════════════════════════
#  CZYSZCZENIE / PARSOWANIE NAZWY FOLDERU
# ═══════════════════════════════════════════════════════════════════════════

# Techniczne "śmieci" które psują wyszukiwanie — usuwane z zapytań
_TECH_PATTERNS = [
    r'\bmp3\b', r'\bm4a\b', r'\bmp4\b', r'\bflac\b', r'\baac\b', r'\bwma\b', r'\bogg\b',
    r'\baudio\s*-?\s*book(?:i|a)?\b', r'\baudiobook(?:i|a)?\b', r'\bebook(?:i)?\b',
    r'\bretail\b', r'\brip\b', r'\bunabridged\b', r'\bpelna\s+wersja\b', r'\bpełna\s+wersja\b',
    r'\d+\s*kbps\b', r'\d+\s*kb/s\b', r'\bchomikuj(?:\.pl)?\b', r'\btorrent\b', r'\bzip\b', r'\brar\b',
    r'\bpol(?:ski|ska)?\b', r'\bpl\b',
]

def _strip_tech(text: str) -> str:
    """Usuwa techniczne oznaczenia (format, jakość, źródło) z tekstu."""
    t = text
    for p in _TECH_PATTERNS:
        t = re.sub(p, ' ', t, flags=re.I)
    t = re.sub(r'[\[\]{}]', ' ', t)
    # puste nawiasy po wycięciu środka
    t = re.sub(r'\(\s*\)', ' ', t)
    t = re.sub(r'_+', ' ', t)                 # podkreślniki zawsze są separatorem
    t = re.sub(r'\.{2,}', ' ', t)              # wielokropki / ciągi kropek
    t = re.sub(r'\s{2,}', ' ', t).strip(' -–—,;:|')
    return t


def _strip_bracketed_junk(text: str) -> str:
    """Usuwa całe grupy [...]/(...) jeśli zawierają wyłącznie techniczne śmieci albo sam rok."""
    def _clean_group(m):
        inner = m.group(1)
        low = inner.lower()
        if re.fullmatch(r'\d{4}', inner.strip()):
            return ' '
        if any(re.search(p, low) for p in _TECH_PATTERNS):
            return ' '
        return m.group(0)
    text = re.sub(r'\[([^\]]+)\]', _clean_group, text)
    text = re.sub(r'\(([^)]+)\)', _clean_group, text)
    return text


_NARRATOR_PATTERNS = [
    r'\[\s*(?:czyta|lektor)\s*[:\-]?\s*([^\]]+)\]',
    r'\(\s*(?:czyta|lektor)\s*[:\-]?\s*([^)]+)\)',
    r'(?:^|[\s,;\-–—])czyta(?:j[ąa])?\s*[:\-]?\s+(.+)$',
    r'(?:^|[\s,;\-–—])lektor\s*[:\-]?\s+(.+)$',
]

# "czyta/czytają autor(zy/ka/ki/ów)" — audiobook czytany przez samego autora/autorów;
# to nie jest imię i nazwisko lektora, więc obsługujemy osobno (narrator = autor).
# "j[ąa]" łapie zarówno "czytają" jak i "czytaja" (bez polskiego znaku — częste
# w nazwach folderów z torrentów/starych archiwów o okrojonym kodowaniu znaków)
_NARRATOR_IS_AUTHOR_RE = re.compile(
    r'(?:^|[\s,;\-–—])czyta(?:j[ąa])?\s+autor(?:zy|ka|ki|ów)?\.?\s*$', re.I)


def _extract_narrator(name: str):
    """Wyciąga lektora z nazwy folderu, zwraca (lektor, nazwa_bez_lektora)."""
    m = _NARRATOR_IS_AUTHOR_RE.search(name)
    if m:
        rest = name[:m.start()].strip()
        return "__AUTOR__", rest  # rozwiązywane później, gdy znamy autora
    for pat in _NARRATOR_PATTERNS:
        m = re.search(pat, name, re.I)
        if m:
            narrator = m.group(1).strip(" .,;:-–—[]()")
            narrator = _strip_tech(narrator)
            # nie bierz zdań-śmieci dłuższych niż typowe imię+nazwisko (maks. 4 słowa)
            words = narrator.split()
            if 1 <= len(words) <= 5 and narrator:
                rest = (name[:m.start()] + " " + name[m.end():]).strip()
                rest = re.sub(r'\s{2,}', ' ', rest)
                return narrator.title(), rest
    return "", name


def _fix_name_order(part: str) -> str:
    """'Nazwisko Imię' → 'Imię Nazwisko', tylko gdy wygląda na nazwisko-najpierw (2-4 słowa z wielkiej litery)."""
    words = part.split()
    if 2 <= len(words) <= 4 and all(w and w[0].isupper() and w[1:].islower() for w in words if len(w) > 1):
        return " ".join([words[-1]] + words[:-1])
    return part


_LEADING_INDEX_RE = re.compile(r'^\s*\d{1,3}[\s._\-\)]+')

def parse_folder(name: str) -> dict:
    """
    Rozpoznaje z nazwy folderu autora, tytuł i lektora. Obsługuje m.in.:
      "Rose Lucy - Jagnię czyta Agnieszka Baranowska"
      "King Stephen - To (czyta Piotr Grabowski) [MP3 128kbps]"
      "Autor - Tytuł [Lektor: Jan Kowalski] AUDIOBOOK PL"
      "Autor.Tytul.czyta.Lektor.PL.AUDIOBOOK" (styl scenowy z kropkami)
      "01. Autor - Tytuł [Czyta Lektor]" (z numerem porządkowym na początku)
      "Pink Floyd - Dark Side of the Moon"
      "Władca Pierścieni"
    """
    raw = name.strip()
    working = raw.rstrip(".")
    working = _LEADING_INDEX_RE.sub('', working)

    # styl scenowy "Autor.Tytul.czyta.Lektor" — kropki/podkreślniki pełnią rolę spacji
    if working.count('.') + working.count('_') >= 2 and working.count(' ') <= (working.count('.') + working.count('_')):
        working = re.sub(r'(?<=\w)[._](?=\w)', ' ', working)

    narrator, working = _extract_narrator(working)
    working = _strip_bracketed_junk(working)
    core = _strip_tech(working)

    info = {"raw": raw, "narrator": narrator, "type": "unknown"}

    # separator autor/tytuł: najpierw myślnik/dwukropek OTOCZONY SPACJAMI (" - "),
    # żeby nie łapać się na krótki myślnik w dwuczłonowym nazwisku typu
    # "Barton-Smoczyńska" albo "Toeplitz-Cieślak" — dopiero gdy takiego nie ma,
    # próbujemy luźniejszego dopasowania (dla rzadkich nazw bez spacji wokół myślnika)
    m = re.match(r'^(.+?)\s+[-–—]\s+(.+)$', core)
    if not m:
        m = re.match(r'^(.+?):\s*(.+)$', core)
    if not m:
        m = re.match(r'^(.+?)\s*[-–—:]\s*(.+)$', core)
    if m:
        left, right = m.group(1).strip(), m.group(2).strip()
        author = _fix_name_order(left)
        info.update({
            "author": author,
            "author_raw": left,
            "title": right,
            "type": "audiobook" if narrator else "unknown",
        })
    else:
        info["author"] = ""
        info["author_raw"] = ""
        info["title"] = core or raw
        info["type"] = "audiobook" if narrator else "unknown"

    # "czyta autor/autorzy" — narrator to w rzeczywistości sam/sami autor(zy)
    if info.get("narrator") == "__AUTOR__":
        info["narrator"] = info.get("author") or info.get("author_raw") or ""

    a  = info.get("author", "")
    ar = info.get("author_raw", a)
    t  = info.get("title", "")

    variants = [
        f"{a} {t}".strip(),
        f"{t} {a}".strip(),
        f"{ar} {t}".strip(),
        t,
        core,
    ]
    seen, query_variants = set(), []
    for v in variants:
        v = re.sub(r'\s{2,}', ' ', v).strip()
        if v and v.lower() not in seen:
            seen.add(v.lower())
            query_variants.append(v)

    info["q_full"]     = query_variants[0] if query_variants else raw
    info["q_title"]    = t or raw
    info["q_title_ab"] = f"{t} audiobook".strip()
    info["query_variants"] = query_variants or [raw]

    return info


def natural_key(s: str):
    """Klucz do naturalnego sortowania (Rozdział 2 przed Rozdział 10)."""
    return [int(part) if part.isdigit() else part.lower()
            for part in re.split(r'(\d+)', s)]


# ═══════════════════════════════════════════════════════════════════════════
#  HTTP HELPER
# ═══════════════════════════════════════════════════════════════════════════

_HDRS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/124.0.0.0 Safari/537.36"
    ),
    "Accept":          "text/html,application/xhtml+xml,application/json,*/*;q=0.9",
    "Accept-Language": "pl-PL,pl;q=0.9,en-US;q=0.8,en;q=0.7",
    "Accept-Encoding": "identity",
}

def _get(url: str, timeout: int = 7, extra_headers: dict = None, retries: int = 0) -> Optional[bytes]:
    last_exc = None
    for attempt in range(retries + 1):
        try:
            h = dict(_HDRS)
            if extra_headers:
                h.update(extra_headers)
            req = urllib.request.Request(url, headers=h)
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return r.read()
        except Exception as e:
            last_exc = e
            continue
    return None


def _find_all_values(obj, keys):
    """Rekurencyjnie zbiera wartości dla podanych kluczy (dowolnie zagnieżdżony JSON)."""
    found = []
    if isinstance(obj, dict):
        for k, v in obj.items():
            if k in keys and isinstance(v, (str, int, float)):
                found.append((k, v))
            else:
                found.extend(_find_all_values(v, keys))
    elif isinstance(obj, list):
        for item in obj:
            found.extend(_find_all_values(item, keys))
    return found


# ═══════════════════════════════════════════════════════════════════════════
#  POLSKIE ŹRÓDŁA WYSZUKIWANIA
# ═══════════════════════════════════════════════════════════════════════════

# ── 1. Lubimyczytac.pl ────────────────────────────────────────────────────

def search_lubimyczytac(query: str) -> list:
    """Scrape lubimyczytac.pl — największa polska baza książek."""
    results = []
    try:
        q = urllib.parse.quote(query)
        url = f"https://lubimyczytac.pl/szukaj/ksiazki?phrase={q}"
        data = _get(url, extra_headers={"Referer": "https://lubimyczytac.pl/"})
        if not data:
            return []
        html = data.decode("utf-8", errors="replace")

        # Tytuły: <a href="https://lubimyczytac.pl/ksiazka/{id}/{slug}" ... title="{Tytuł}">
        title_matches = list(re.finditer(
            r'<a[^>]+href="https?://lubimyczytac\.pl/ksiazka/(\d+)/[^"]*"[^>]*title="([^"]+)"', html))
        # Autorzy: <a href=".../autor/{id}/{slug}">{Autor}</a>
        author_matches = list(re.finditer(
            r'<a[^>]+href="https?://lubimyczytac\.pl/autor/\d+/[^"]*"[^>]*>([^<]*)</a>', html))
        cover_matches = re.findall(
            r'(?:data-src|src)="(https?://s\.lubimyczytac\.pl/upload/books/[^"]+\.(?:jpg|jpeg|png|webp))"', html)

        seen_ids = set()
        cover_idx = 0
        for tm in title_matches:
            book_id = tm.group(1)
            if book_id in seen_ids:
                continue
            seen_ids.add(book_id)
            title = html_mod.unescape(tm.group(2)).strip()
            if not title or len(title) < 2 or len(title) > 150:
                continue

            # najbliższy autor występujący ZA tytułem w kodzie HTML
            author = ""
            for am in author_matches:
                if am.start() > tm.end():
                    author = html_mod.unescape(am.group(1)).strip()
                    break
            if author.lower() == title.lower():
                author = ""

            cover = cover_matches[cover_idx] if cover_idx < len(cover_matches) else ""
            cover_idx += 1

            results.append({
                "title": title, "author": author, "year": "",
                "genre": "Audiobook", "publisher": "",
                "cover_url": cover, "source": "Lubimyczytac",
            })
            if len(results) >= 8:
                break
    except Exception:
        pass
    return results


# ── 2. Audioteka.com/pl ───────────────────────────────────────────────────

def search_audioteka(query: str) -> list:
    """Audioteka — platforma audiobooków po polsku."""
    results = []
    # Próba 1: wewnętrzne API
    try:
        q = urllib.parse.quote(query)
        url = f"https://api2.audioteka.com/v1/catalog/search?q={q}&limit=8&lang=pl"
        data = _get(url, extra_headers={"Accept": "application/json"})
        if data:
            j = json.loads(data)
            items = j.get("items") or j.get("results") or j.get("data") or []
            if not items and isinstance(j, dict):
                # nieznana struktura — spróbuj znaleźć listę słowników z "title"
                for v in j.values():
                    if isinstance(v, list) and v and isinstance(v[0], dict) and "title" in str(v[0]).lower():
                        items = v
                        break
            for item in items[:8]:
                if not isinstance(item, dict):
                    continue
                title = item.get("title") or item.get("name") or ""
                if not title:
                    continue
                cover = item.get("cover", "") or item.get("image", "") or item.get("artwork", "")
                if isinstance(cover, dict):
                    cover = cover.get("url", "") or cover.get("src", "")
                author = item.get("author", "") or item.get("authors", "")
                if isinstance(author, list):
                    author = ", ".join(str(a) for a in author)
                results.append({
                    "title":     title,
                    "author":    author,
                    "year":      str(item.get("releaseYear", "") or item.get("year", "")),
                    "genre":     "Audiobook",
                    "publisher": item.get("publisher", ""),
                    "cover_url": cover,
                    "source":    "Audioteka",
                })
            if results:
                return results
    except Exception:
        pass

    # Próba 2: scrape strony wyszukiwania (JSON-LD)
    try:
        q = urllib.parse.quote(query)
        url = f"https://audioteka.com/pl/szukaj/?query={q}"
        data = _get(url)
        if not data:
            return results
        html = data.decode("utf-8", errors="replace")

        ld_blocks = re.findall(r'<script[^>]+type="application/ld\+json"[^>]*>(.*?)</script>',
                               html, re.S)
        for block in ld_blocks:
            try:
                obj = json.loads(block)
                items = obj if isinstance(obj, list) else [obj]
                for item in items:
                    if item.get("@type") in ("AudioObject", "Book", "Product", "Audiobook"):
                        results.append({
                            "title":     item.get("name", ""),
                            "author":    (item.get("author") or {}).get("name", "") if isinstance(item.get("author"), dict) else str(item.get("author", "")),
                            "year":      str(item.get("datePublished", ""))[:4],
                            "genre":     "Audiobook",
                            "publisher": (item.get("publisher") or {}).get("name", "") if isinstance(item.get("publisher"), dict) else "",
                            "cover_url": item.get("image", ""),
                            "source":    "Audioteka",
                        })
            except Exception:
                pass

        if not results:
            titles  = re.findall(r'class="[^"]*product[^"]*title[^"]*"[^>]*>([^<]+)<', html)
            authors = re.findall(r'class="[^"]*product[^"]*author[^"]*"[^>]*>([^<]+)<', html)
            covers  = re.findall(r'<img[^>]+(?:class="[^"]*product[^"]*image[^"]*"[^>]+)?src="(https?://[^"]+audioteka[^"]+\.(?:jpg|png|webp)[^"]*)"', html)
            for i in range(min(len(titles), 8)):
                results.append({
                    "title":     html_mod.unescape(titles[i].strip()),
                    "author":    html_mod.unescape(authors[i].strip()) if i < len(authors) else "",
                    "year":      "",
                    "genre":     "Audiobook",
                    "publisher": "",
                    "cover_url": covers[i] if i < len(covers) else "",
                    "source":    "Audioteka",
                })
    except Exception:
        pass
    return results


# ── 3. Empik.com ──────────────────────────────────────────────────────────

def search_empik(query: str) -> list:
    """Empik — bogata baza, ale często blokuje automatyczne zapytania (może zwrócić 0 wyników)."""
    results = []
    try:
        q = urllib.parse.quote(query)
        url = f"https://www.empik.com/szukaj/produkt?q={q}&qtype=basicForm&searchCategory=31"
        data = _get(url, extra_headers={"Referer": "https://www.empik.com/"})
        if not data:
            url = f"https://www.empik.com/szukaj/produkt?q={q}&qtype=basicForm"
            data = _get(url)
        if not data:
            return []
        html = data.decode("utf-8", errors="replace")

        nd = re.search(r'<script id="__NEXT_DATA__"[^>]*>(.*?)</script>', html, re.S)
        if nd:
            try:
                page = json.loads(nd.group(1))
                pairs = _find_all_values(page, {"name", "title"})
                covers = [v for k, v in _find_all_values(page, {"imageUrl", "coverUrl", "image", "cover"})
                          if isinstance(v, str) and v.startswith("http")]
                for i, (_, name) in enumerate(pairs[:8]):
                    results.append({
                        "title":     html_mod.unescape(str(name)),
                        "author":    "",
                        "year":      "",
                        "genre":     "Audiobook",
                        "publisher": "",
                        "cover_url": covers[i] if i < len(covers) else "",
                        "source":    "Empik",
                    })
                if results:
                    return results
            except Exception:
                pass

        titles  = re.findall(r'<span[^>]+class="[^"]*ta-product-name[^"]*"[^>]*>([^<]+)<', html)
        covers  = re.findall(r'<img[^>]+class="[^"]*product-image[^"]*"[^>]+src="([^"]+)"', html)
        authors = re.findall(r'<span[^>]+class="[^"]*smartAuthor[^"]*"[^>]*>([^<]+)<', html)
        for i in range(min(len(titles), 8)):
            results.append({
                "title":     html_mod.unescape(titles[i].strip()),
                "author":    html_mod.unescape(authors[i].strip()) if i < len(authors) else "",
                "year":      "",
                "genre":     "Audiobook",
                "publisher": "",
                "cover_url": covers[i] if i < len(covers) else "",
                "source":    "Empik",
            })
    except Exception:
        pass
    return results


# ── 4. Google Books (z filtrem polskim) ───────────────────────────────────

def search_google_books(query: str, lang_pl: bool = True) -> list:
    results = []
    try:
        q = urllib.parse.quote(query)
        lang = "&langRestrict=pl" if lang_pl else ""
        url = f"https://www.googleapis.com/books/v1/volumes?q={q}&maxResults=8{lang}"
        data = _get(url)
        if not data:
            return []
        for item in json.loads(data).get("items", []):
            vi = item.get("volumeInfo", {})
            cover = ""
            for sz in ("extraLarge", "large", "medium", "thumbnail", "smallThumbnail"):
                raw = vi.get("imageLinks", {}).get(sz, "")
                if raw:
                    cover = raw.replace("http://", "https://")
                    cover = re.sub(r'zoom=\d', 'zoom=3', cover).replace("&edge=curl", "")
                    break
            results.append({
                "title":       vi.get("title", ""),
                "author":      ", ".join(vi.get("authors", [])),
                "year":        vi.get("publishedDate", "")[:4],
                "genre":       (vi.get("categories") or [""])[0][:40],
                "publisher":   vi.get("publisher", ""),
                "cover_url":   cover,
                "description": (vi.get("description") or "").strip(),
                "source":      "Google Books PL" if lang_pl else "Google Books",
            })
    except Exception:
        pass
    return results


# ── 5. Open Library ───────────────────────────────────────────────────────

def search_openlibrary(query: str) -> list:
    results = []
    try:
        q = urllib.parse.quote(query)
        url = (f"https://openlibrary.org/search.json?q={q}&limit=6"
               f"&fields=title,author_name,first_publish_year,subject,cover_i,publisher")
        data = _get(url)
        if not data:
            return []
        for doc in json.loads(data).get("docs", []):
            cover = (f"https://covers.openlibrary.org/b/id/{doc['cover_i']}-L.jpg"
                     if doc.get("cover_i") else "")
            results.append({
                "title":     doc.get("title", ""),
                "author":    (doc.get("author_name") or [""])[0],
                "year":      str(doc.get("first_publish_year", "")),
                "genre":     (doc.get("subject") or [""])[0][:40],
                "publisher": (doc.get("publisher") or [""])[0],
                "cover_url": cover,
                "source":    "Open Library",
            })
    except Exception:
        pass
    return results


# ── 6. iTunes ─────────────────────────────────────────────────────────────

def search_itunes(query: str) -> list:
    results = []
    for entity in ("audiobook", "album"):
        try:
            q = urllib.parse.quote(query)
            url = f"https://itunes.apple.com/search?term={q}&limit=5&entity={entity}&country=pl"
            data = _get(url)
            if not data:
                continue
            for item in json.loads(data).get("results", []):
                cover = item.get("artworkUrl100", "")
                if cover:
                    cover = re.sub(r'\d+x\d+', '600x600', cover)
                results.append({
                    "title":     item.get("collectionName") or item.get("trackName", ""),
                    "author":    item.get("artistName", ""),
                    "year":      item.get("releaseDate", "")[:4],
                    "genre":     item.get("primaryGenreName", ""),
                    "publisher": "",
                    "cover_url": cover,
                    "source":    "iTunes",
                })
        except Exception:
            pass
        if results:
            break
    return results


def search_wikipedia_pl(query: str) -> list:
    """Szuka na polskiej Wikipedii (stabilne REST API) — dobre uzupełnienie: opis, tytuł.

    UWAGA: celowo NIE używamy tu miniatury (thumbnail) jako okładki. Artykuły o książkach
    na Wikipedii (zwłaszcza starszych/klasycznych) bardzo często nie mają wgranej okładki
    i zamiast niej w infoboksie/artykule pojawia się PORTRET AUTORA — co przy naiwnym
    użyciu prowadziłoby do wklejenia zdjęcia autora zamiast okładki książki. Wikipedia
    służy tu tylko jako gwarantowane źródło tytułu/opisu, nigdy obrazka."""
    results = []
    try:
        q = urllib.parse.quote(query)
        url = f"https://pl.wikipedia.org/w/rest.php/v1/search/page?q={q}&limit=5"
        data = _get(url, extra_headers={"Accept": "application/json"})
        if not data:
            return results
        pages = json.loads(data).get("pages", [])
        for p in pages:
            title = p.get("title", "")
            if not title:
                continue
            desc = p.get("description") or ""
            excerpt = html_mod.unescape(re.sub(r'<[^>]+>', '', p.get("excerpt") or ""))
            results.append({
                "title":       title,
                "author":      "",
                "year":        "",
                "genre":       "",  # opis artykułu to nie gatunek — nie wpisujemy śmieci do tagu
                "publisher":   "",
                "cover_url":   "",  # patrz UWAGA w docstringu — nigdy nie bierzemy stąd obrazka
                "description": excerpt or desc,
                "source":      "Wikipedia PL",
            })
    except Exception:
        pass
    return results


def _extract_jsonld_books(html_text: str, source_name: str) -> list:
    """Wyciąga dane książek/produktów ze znaczników JSON-LD (schema.org Book/Product) —
    odporne na zmiany klas CSS, bo opiera się na ustrukturyzowanych danych, nie na wyglądzie strony."""
    results = []
    try:
        for m in re.finditer(
                r'<script[^>]+type=["\']application/ld\+json["\'][^>]*>(.*?)</script>',
                html_text, re.S | re.I):
            raw = html_mod.unescape(m.group(1).strip())
            try:
                data = json.loads(raw)
            except Exception:
                continue
            items = data if isinstance(data, list) else [data]
            for item in items:
                if not isinstance(item, dict):
                    continue
                graph = item.get("@graph")
                candidates = graph if isinstance(graph, list) else [item]
                for obj in candidates:
                    if not isinstance(obj, dict):
                        continue
                    typ = obj.get("@type", "")
                    typ_s = " ".join(typ) if isinstance(typ, list) else str(typ)
                    if not re.search(r'Book|Product|Audiobook', typ_s, re.I):
                        continue
                    name = obj.get("name", "")
                    if not name:
                        continue
                    author = obj.get("author", "")
                    if isinstance(author, dict):
                        author = author.get("name", "")
                    elif isinstance(author, list):
                        author = ", ".join(
                            a.get("name", "") if isinstance(a, dict) else str(a) for a in author)
                    image = obj.get("image", "")
                    if isinstance(image, list):
                        image = image[0] if image else ""
                    if isinstance(image, dict):
                        image = image.get("url", "")
                    publisher = obj.get("publisher", "")
                    if isinstance(publisher, dict):
                        publisher = publisher.get("name", "")
                    results.append({
                        "title":     str(name).strip(),
                        "author":    str(author).strip(),
                        "year":      "",
                        "genre":     "",
                        "publisher": str(publisher).strip(),
                        "cover_url": str(image).strip(),
                        "source":    source_name,
                    })
    except Exception:
        pass
    return results


def search_nexto(query: str) -> list:
    """Nexto.pl (ebooki/audiobooki) — wyszukiwanie 'najlepszego wysiłku': adresu wyszukiwania
    nie dało się zweryfikować na żywo w tym środowisku, więc funkcja może zwracać 0 wyników,
    jeśli strona zmieniła strukturę/adres. Nigdy nie przerywa działania programu."""
    results = []
    try:
        q = urllib.parse.quote(query)
        url = f"https://www.nexto.pl/szukaj?q={q}"
        data = _get(url)
        if not data:
            return results
        results = _extract_jsonld_books(data.decode("utf-8", "ignore"), "Nexto")[:5]
    except Exception:
        pass
    return results


def search_taniaksiazka(query: str) -> list:
    """TaniaKsiazka.pl — j.w., wyszukiwanie 'najlepszego wysiłku' (adres strony niezweryfikowany
    na żywo w tym środowisku). Może zwracać 0 wyników bez wpływu na resztę programu."""
    results = []
    try:
        q = urllib.parse.quote(query)
        url = f"https://www.taniaksiazka.pl/szukaj?q={q}"
        data = _get(url)
        if not data:
            return results
        results = _extract_jsonld_books(data.decode("utf-8", "ignore"), "TaniaKsiazka")[:5]
    except Exception:
        pass
    return results


# ── Dopasowanie najlepszego wyniku ──────────────────────────────────────────

def score_result(r: dict, info: dict) -> float:
    """Ocena podobieństwa wyniku wyszukiwania do tego, co rozpoznano z nazwy folderu."""
    t_r = (r.get("title") or "").lower().strip()
    a_r = (r.get("author") or "").lower().strip()
    t_i = (info.get("title") or "").lower().strip()
    a_i = (info.get("author") or "").lower().strip()

    score = difflib.SequenceMatcher(None, t_r, t_i).ratio() * 0.7
    if a_i and a_r:
        score += difflib.SequenceMatcher(None, a_r, a_i).ratio() * 0.3
    elif a_i or a_r:
        score += 0.05
    if r.get("cover_url"):
        score += 0.03
    return score


# ── Okładka ───────────────────────────────────────────────────────────────

def download_cover(url: str) -> Optional[bytes]:
    if not url:
        return None
    data = _get(url, timeout=15, retries=1)
    return data if (data and len(data) > 1500) else None


# ═══════════════════════════════════════════════════════════════════════════
#  ZAPIS TAGÓW  (autor/tytuł/rok/gatunek + LEKTOR jako "Composer" —
#  tak Plex i większość aplikacji audiobookowych rozpoznaje narratora)
# ═══════════════════════════════════════════════════════════════════════════

def _comment_text(tags: dict) -> str:
    parts = []
    if tags.get("narrator"):   parts.append(f"Czyta: {tags['narrator']}")
    if tags.get("publisher"):  parts.append(f"Wydawca: {tags['publisher']}")
    header = "; ".join(parts)
    desc = (tags.get("description") or "").strip()
    if header and desc:
        return f"{header}\n\n{desc}"
    return header or desc


def write_mp3(path, tags, cover, num, total):
    try:    audio = ID3(path)
    except ID3NoHeaderError: audio = ID3()
    def s(cls, key, val):
        if val: audio[key] = cls(encoding=3, text=str(val))
    s(TIT2, "TIT2", tags.get("title", ""))
    s(TPE1, "TPE1", tags.get("author", ""))
    s(TPE2, "TPE2", tags.get("author", ""))
    s(TALB, "TALB", tags.get("album", tags.get("title", "")))
    s(TDRC, "TDRC", tags.get("year", ""))
    s(TCON, "TCON", tags.get("genre", "Audiobook"))
    s(TCOM, "TCOM", tags.get("narrator", ""))
    if num > 0: audio["TRCK"] = TRCK(encoding=3, text=f"{num}/{total}")
    cmt = _comment_text(tags)
    if cmt:
        audio.delall("COMM")
        audio["COMM::pol"] = COMM(encoding=3, lang="pol", desc="", text=cmt)
    if cover:
        audio.delall("APIC")
        audio["APIC:"] = APIC(encoding=3, mime="image/jpeg", type=3, desc="Cover", data=cover)
    audio.save(path, v2_version=3)


def write_flac(path, tags, cover, num, total):
    audio = FLAC(path); audio.clear()
    if tags.get("title"):    audio["title"]       = tags["title"]
    if tags.get("author"):   audio["artist"]      = tags["author"]; audio["albumartist"] = tags["author"]
    audio["album"] = tags.get("album", tags.get("title", ""))
    if tags.get("year"):     audio["date"]        = str(tags["year"])
    audio["genre"] = tags.get("genre", "Audiobook")
    if tags.get("narrator"): audio["composer"]    = tags["narrator"]
    if num > 0:              audio["tracknumber"] = str(num); audio["totaltracks"] = str(total)
    cmt = _comment_text(tags)
    if cmt:                  audio["comment"] = cmt
    if cover:
        p = Picture(); p.type = 3; p.mime = "image/jpeg"; p.desc = "Cover"; p.data = cover
        audio.clear_pictures(); audio.add_picture(p)
    audio.save()


def write_m4a(path, tags, cover, num, total):
    audio = MP4(path)
    if tags.get("title"):    audio["\xa9nam"] = [tags["title"]]
    if tags.get("author"):   audio["\xa9ART"] = [tags["author"]]
    audio["\xa9alb"] = [tags.get("album", tags.get("title", ""))]
    if tags.get("year"):     audio["\xa9day"] = [str(tags["year"])]
    audio["\xa9gen"] = [tags.get("genre", "Audiobook")]
    if tags.get("narrator"): audio["\xa9wrt"] = [tags["narrator"]]   # Composer = Lektor
    if num > 0:              audio["trkn"] = [(num, total)]
    cmt = _comment_text(tags)
    if cmt:                  audio["\xa9cmt"] = [cmt]
    if cover:                audio["covr"] = [MP4Cover(cover, imageformat=MP4Cover.FORMAT_JPEG)]
    audio.save()


def write_ogg(path, tags, cover, num, total):
    if not _OGG:
        raise RuntimeError("Brak modułu OggVorbis w mutagen")
    audio = OggVorbis(path)
    if tags.get("title"):    audio["title"]       = tags["title"]
    if tags.get("author"):   audio["artist"]      = tags["author"]; audio["albumartist"] = tags["author"]
    audio["album"] = tags.get("album", tags.get("title", ""))
    if tags.get("year"):     audio["date"]        = str(tags["year"])
    audio["genre"] = tags.get("genre", "Audiobook")
    if tags.get("narrator"): audio["composer"]    = tags["narrator"]
    if num > 0:              audio["tracknumber"] = str(num); audio["totaltracks"] = str(total)
    cmt = _comment_text(tags)
    if cmt:                  audio["comment"] = cmt
    if cover:
        pic = Picture()
        pic.type = 3; pic.mime = "image/jpeg"; pic.desc = "Cover"; pic.data = cover
        audio["metadata_block_picture"] = [base64.b64encode(pic.write()).decode("ascii")]
    audio.save()


# Opóźnienia (s) między ponownymi próbami, gdy plik jest chwilowo zablokowany
# przez inny program (Plex skanujący bibliotekę, antywirus, odtwarzacz, podgląd Eksploratora)
_LOCK_RETRY_DELAYS = (0.5, 1.0, 2.0, 4.0)


def _is_lock_error(e) -> bool:
    """True, jeśli błąd oznacza 'plik używany przez inny proces' / brak dostępu (Windows 5/32/33)."""
    depth = 0
    while e is not None and depth < 6:
        if isinstance(e, PermissionError) or getattr(e, "winerror", None) in (5, 32, 33):
            return True
        if getattr(e, "args", None) and isinstance(e.args[0], BaseException):
            e = e.args[0]
        else:
            e = e.__cause__ or e.__context__
        depth += 1
    return False


def write_tags(path, tags, cover, num=0, total=0):
    """Zwraca (True, '') przy sukcesie albo (False, powod) przy błędzie/braku wsparcia."""
    if not tags.get("year"):
        # Nie znaleziono roku wydania w żadnym źródle — zamiast zostawiać puste pole,
        # wpisujemy bieżący rok (datę "wgrania"/przygotowania pliku), żeby żaden
        # audiobook nie został bez roku w bibliotece Plex.
        tags = dict(tags)
        tags["year"] = time.strftime("%Y")
    ext = Path(path).suffix.lower()
    writer = {".mp3": write_mp3, ".flac": write_flac, ".m4a": write_m4a,
              ".aac": write_m4a, ".ogg": write_ogg}.get(ext)
    if writer is None:
        return False, "nieobsługiwany format"
    for attempt in range(len(_LOCK_RETRY_DELAYS) + 1):
        try:
            writer(path, tags, cover, num, total)
            return True, ""
        except Exception as e:
            if _is_lock_error(e) and attempt < len(_LOCK_RETRY_DELAYS):
                _flog.warning("Plik zablokowany (próba %d), ponawiam: %s — %s", attempt + 1, path, e)
                time.sleep(_LOCK_RETRY_DELAYS[attempt])
                continue
            _flog.error("Błąd zapisu tagów: %s", path, exc_info=True)
            reason = f"{type(e).__name__}: {e}"
            if _is_lock_error(e):
                reason += (" — plik jest używany przez inny program "
                           "(Plex, odtwarzacz, antywirus, podgląd w Eksploratorze?)")
            return False, reason
    return False, "nieznany błąd"


def get_audio_files(folder: str) -> list:
    try:
        recover_tmp_files(folder)
    except Exception:
        _flog.error("Błąd sprzątania plików tymczasowych w %s", folder, exc_info=True)
    files = [str(f) for f in Path(folder).iterdir()
             if f.is_file() and f.suffix.lower() in AUDIO_EXT]
    files.sort(key=lambda p: natural_key(Path(p).name))
    return files


# ═══════════════════════════════════════════════════════════════════════════
#  OKŁADKA Z SAMEGO FOLDERU — jeśli ten, kto przygotował audiobooka, dołączył
#  własny obrazek, jest on praktycznie zawsze prawdziwą, oryginalną okładką —
#  pewniejszą niż cokolwiek znalezione w internecie.
# ═══════════════════════════════════════════════════════════════════════════

_COVER_IMAGE_EXT = {'.jpg', '.jpeg', '.png', '.webp', '.bmp', '.gif', '.tiff', '.tif'}


def find_local_cover_image(folder: str) -> Optional[str]:
    """Jeśli folder z audiobookiem zawiera DOKŁADNIE JEDEN plik graficzny (bez względu na
    nazwę), to niemal na pewno oryginalna okładka — używamy jej od razu, bez czekania na
    wyszukiwanie w internecie. Gdy jest ich więcej niż jeden, nie zgadujemy który to okładka."""
    try:
        images = sorted(f for f in Path(folder).iterdir()
                         if f.is_file() and f.suffix.lower() in _COVER_IMAGE_EXT)
        if len(images) == 1:
            return str(images[0])
    except Exception:
        pass
    return None


def load_image_as_jpeg_cover(path: str) -> Optional[bytes]:
    """Wczytuje dowolny obraz z dysku i konwertuje na JPEG nadający się jako okładka (APIC)."""
    try:
        img = Image.open(path)
        img.load()
        if img.mode not in ("RGB", "L"):
            img = img.convert("RGB")
        buf = BytesIO()
        img.save(buf, format="JPEG", quality=92)
        return buf.getvalue()
    except Exception:
        return None


# ═══════════════════════════════════════════════════════════════════════════
#  ZMIANA KOLEJNOŚCI / NUMEROWANIE PLIKÓW  (01 - ... → dla Plex/audiobooków)
# ═══════════════════════════════════════════════════════════════════════════

_LEADING_NUM_RE = re.compile(r'^\s*(?:cz(?:ęść|esc)?\.?\s*)?\d{1,4}[\s._\-]+', re.I)

def plan_renumber(files: list) -> list:
    """Zwraca listę (stara_ścieżka, nowa_ścieżka) po naturalnym posortowaniu i ponumerowaniu 01..N."""
    ordered = sorted(files, key=lambda p: natural_key(Path(p).name))
    total = len(ordered)
    width = max(2, len(str(total)))
    plan = []
    used_names = set()
    for i, p in enumerate(ordered, 1):
        pp = Path(p)
        stem_clean = _LEADING_NUM_RE.sub('', pp.stem).strip(' -._') or pp.stem
        base = f"{i:0{width}d} - {stem_clean}"
        new_name = base + pp.suffix
        # unikaj kolizji nazw (np. dwa pliki o identycznym stem po oczyszczeniu)
        n = 1
        while new_name.lower() in used_names:
            n += 1
            new_name = f"{base} ({n}){pp.suffix}"
        used_names.add(new_name.lower())
        plan.append((str(pp), str(pp.parent / new_name)))
    return plan


TMP_SUFFIX = ".__audiotagai_tmp__"


def _rename_retry(src, dst):
    """os.rename z ponowieniem, gdy plik jest chwilowo zablokowany przez inny program."""
    for attempt in range(len(_LOCK_RETRY_DELAYS) + 1):
        try:
            os.rename(src, dst)
            return
        except OSError as e:
            if _is_lock_error(e) and attempt < len(_LOCK_RETRY_DELAYS):
                time.sleep(_LOCK_RETRY_DELAYS[attempt])
                continue
            raise


def apply_renumber(plan: list) -> list:
    """Zmienia nazwy plików wg planu i zwraca nowe ścieżki w kolejności planu.

    Pliki są przemianowywane BEZPOŚREDNIO (stara nazwa → nowa), bez plików tymczasowych.
    Tymczasowa nazwa (*.__audiotagai_tmp__) jest używana tylko w rzadkim przypadku,
    gdy dwa pliki „zamieniają się” nazwami. Jeśli cokolwiek się nie uda (np. plik
    zablokowany przez Plex/antywirus), WSZYSTKIE zmiany są cofane — w folderze nie
    zostają żadne pliki tymczasowe ani pół-przemianowane pliki."""
    norm = lambda p: os.path.normcase(os.path.abspath(p))
    pending = {norm(o): (o, n) for o, n in plan if norm(o) != norm(n)}
    done = []          # (skąd, dokąd) — do ewentualnego wycofania
    try:
        progress = True
        while pending and progress:
            progress = False
            for key in list(pending):
                old, new = pending[key]
                # cel wolny (i nie jest nazwą innego pliku, który jeszcze czeka)?
                if norm(new) not in pending and not os.path.exists(new):
                    _rename_retry(old, new)
                    done.append((old, new))
                    del pending[key]
                    progress = True
        if pending:
            # zostały tylko "cykle" (pliki zamieniające się nazwami) albo cel zajęty
            # przez obcy plik — rozwiązujemy przez nazwy tymczasowe
            tmp_moves = []
            for key, (old, new) in list(pending.items()):
                if os.path.exists(new) and norm(new) not in pending:
                    raise FileExistsError(f"Plik docelowy już istnieje: {Path(new).name}")
                tmp = old + TMP_SUFFIX
                _rename_retry(old, tmp)
                done.append((old, tmp))
                tmp_moves.append((tmp, new))
            for tmp, new in tmp_moves:
                _rename_retry(tmp, new)
                done.append((tmp, new))
    except Exception:
        _flog.error("Numerowanie plików nie powiodło się — cofam zmiany", exc_info=True)
        for src, dst in reversed(done):
            try:
                _rename_retry(dst, src)
            except Exception:
                _flog.error("Nie udało się cofnąć: %s -> %s", dst, src, exc_info=True)
        raise
    return [new for _old, new in plan]


def _audio_length(path) -> float:
    try:
        a = mutagen.File(path)
        return float(getattr(getattr(a, "info", None), "length", 0) or 0)
    except Exception:
        return 0.0


def recover_tmp_files(folder: str) -> dict:
    """Sprząta pliki *.__audiotagai_tmp__ pozostawione przez starsze wersje programu.

    - jeśli w folderze jest już ponumerowany odpowiednik (np. '05 - Tytuł.mp3' dla
      '05. Tytuł.mp3.__audiotagai_tmp__') o tej samej długości nagrania — tmp to zbędna
      kopia i zostaje usunięty,
    - jeśli odpowiednika nie ma — plik wraca do swojej oryginalnej nazwy (nic nie ginie),
    - w razie wątpliwości plik zostaje nietknięty (i jest to zapisane w dzienniku)."""
    out = {"deleted": [], "restored": [], "kept": []}
    folder_p = Path(folder)
    tmps = [f for f in folder_p.iterdir() if f.is_file() and f.name.endswith(TMP_SUFFIX)]
    if not tmps:
        return out
    audio = [f for f in folder_p.iterdir()
             if f.is_file() and f.suffix.lower() in AUDIO_EXT]
    by_stem = {}
    for f in audio:
        clean = _LEADING_NUM_RE.sub('', f.stem).strip(' -._').lower()
        by_stem.setdefault((clean, f.suffix.lower()), []).append(f)
    for t in tmps:
        orig = t.with_name(t.name[:-len(TMP_SUFFIX)])
        clean = _LEADING_NUM_RE.sub('', orig.stem).strip(' -._').lower()
        num_m = re.match(r'^\s*(\d+)', orig.stem)
        twins = by_stem.get((clean, orig.suffix.lower()), [])
        twin = None
        t_len = _audio_length(t)
        for cand in twins:
            c_num = re.match(r'^\s*(\d+)', cand.stem)
            same_num = (not num_m or not c_num or int(num_m.group(1)) == int(c_num.group(1)))
            if same_num and t_len > 0 and abs(_audio_length(cand) - t_len) <= 2.0:
                twin = cand
                break
        try:
            if twin is not None:
                os.remove(t)
                out["deleted"].append(t.name)
                _flog.info("Usunięto zbędną kopię tymczasową %s (jest już %s)", t.name, twin.name)
            elif not orig.exists():
                _rename_retry(str(t), str(orig))
                out["restored"].append(orig.name)
                _flog.info("Przywrócono %s -> %s", t.name, orig.name)
            else:
                out["kept"].append(t.name)
                _flog.warning("Pozostawiono %s — nie wiadomo, czy to duplikat", t.name)
        except Exception:
            out["kept"].append(t.name)
            _flog.error("Nie udało się posprzątać %s", t, exc_info=True)
    return out


# ═══════════════════════════════════════════════════════════════════════════
#  FUNKCJE "PREMIUM" — ikona, statystyki, historia folderów, ładniejsza okładka
#  (czysto dodatkowe — nie ruszają logiki wyszukiwania/tagowania powyżej)
# ═══════════════════════════════════════════════════════════════════════════

def _resource_dir() -> Path:
    """Folder obok skryptu / zbudowanego .exe — do zapisu ikony, historii itp."""
    try:
        if getattr(sys, "frozen", False):
            return Path(sys.executable).resolve().parent
        return Path(__file__).resolve().parent
    except Exception:
        return Path(".")


# ── Plik dziennika (audiotagai_dziennik.log) ────────────────────────────────
# Wcześniej "dziennik" istniał tylko jako panel w oknie programu — po zamknięciu
# znikał, a szczegóły błędów (np. z kolejki) w ogóle nie były nigdzie zapisywane.

_flog = logging.getLogger("AudioTagAI")
_flog.addHandler(logging.NullHandler())
LOG_FILE: Optional[Path] = None


def _log_dir() -> Path:
    """Obok programu; jeśli tam nie wolno pisać — %LOCALAPPDATA%\\AudioTagAI."""
    la = os.environ.get("LOCALAPPDATA") or os.path.expanduser("~")
    for d in (_resource_dir(), Path(la) / "AudioTagAI"):
        try:
            d.mkdir(parents=True, exist_ok=True)
            probe = d / ".audiotagai_test"
            probe.write_text("x", encoding="utf-8")
            probe.unlink()
            return d
        except Exception:
            continue
    return Path(".")


def setup_file_log():
    global LOG_FILE
    try:
        LOG_FILE = _log_dir() / "audiotagai_dziennik.log"
        h = RotatingFileHandler(LOG_FILE, maxBytes=2_000_000, backupCount=3, encoding="utf-8")
        h.setFormatter(logging.Formatter("%(asctime)s  %(levelname)-7s [%(threadName)s]  %(message)s"))
        _flog.addHandler(h)
        _flog.setLevel(logging.DEBUG)
        _flog.info("===== AudioTagAI %s — start =====", APP_VERSION)
    except Exception:
        LOG_FILE = None

    def _thread_hook(args):
        _flog.error("Nieobsłużony wyjątek w wątku %s", getattr(args.thread, "name", "?"),
                    exc_info=(args.exc_type, args.exc_value, args.exc_traceback))
    threading.excepthook = _thread_hook
    sys.excepthook = lambda t, v, tb: _flog.error("Nieobsłużony wyjątek", exc_info=(t, v, tb))


def generate_icon_image(size: int = 256) -> "Image.Image":
    """Rysuje logo AudioTagAI (słuchawki na gradiencie) czysto w PIL — bez zewnętrznych plików/grafik."""
    img = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    pad = int(size * 0.03)
    grad = Image.new("RGBA", (size, size), (0, 0, 0, 255))
    gd = ImageDraw.Draw(grad)
    for y in range(size):
        t = y / max(1, size - 1)
        r = int(0x7c + (0x22 - 0x7c) * t)
        g = int(0x6a + (0xd3 - 0x6a) * t)
        b = int(0xf7 + (0xc9 - 0xf7) * t)
        gd.line([(0, y), (size, y)], fill=(r, g, b, 255))
    mask = Image.new("L", (size, size), 0)
    ImageDraw.Draw(mask).rounded_rectangle([pad, pad, size - pad, size - pad],
                                            radius=int(size * 0.24), fill=255)
    img.paste(grad, (0, 0), mask)
    d = ImageDraw.Draw(img)
    cx, cy = size // 2, int(size * 0.42)
    r = int(size * 0.26)
    band_w = max(4, int(size * 0.06))
    d.arc([cx - r, cy - r, cx + r, cy + r], start=195, end=345, fill="white", width=band_w)
    ear_w, ear_h = int(size * 0.17), int(size * 0.26)
    for ang_deg in (195, 345):
        rad = math.radians(ang_deg)
        ex = cx + r * math.cos(rad)
        ey = cy + r * math.sin(rad) + ear_h * 0.28
        d.rounded_rectangle([ex - ear_w / 2, ey - ear_h / 2, ex + ear_w / 2, ey + ear_h / 2],
                             radius=ear_w * 0.4, fill="white")
    return img


def get_or_create_icon_path() -> Optional[Path]:
    """Zwraca ścieżkę do AudioTagAI.ico (tworzy przy pierwszym uruchomieniu, jeśli brak)."""
    try:
        path = _resource_dir() / "AudioTagAI.ico"
        if path.exists():
            return path
        img = generate_icon_image(256)
        img.save(path, format="ICO", sizes=[(16, 16), (24, 24), (32, 32), (48, 48), (64, 64), (128, 128), (256, 256)])
        return path
    except Exception:
        return None


def rounded_shadow_cover(data: bytes, box: int = 172, radius: int = 20) -> Optional["ImageTk.PhotoImage"]:
    """Buduje ładną miniaturę okładki: zaokrąglone rogi + miękki cień, gotową do wstawienia w Label."""
    try:
        img = Image.open(BytesIO(data)).convert("RGB")
        img = ImageOps.fit(img, (box, box), Image.LANCZOS)

        mask = Image.new("L", (box, box), 0)
        ImageDraw.Draw(mask).rounded_rectangle([0, 0, box - 1, box - 1], radius=radius, fill=255)
        rounded = Image.new("RGBA", (box, box), (0, 0, 0, 0))
        rounded.paste(img, (0, 0), mask)

        pad = 14
        canvas = Image.new("RGBA", (box + pad * 2, box + pad * 2), (0, 0, 0, 0))
        shadow = Image.new("RGBA", canvas.size, (0, 0, 0, 0))
        ImageDraw.Draw(shadow).rounded_rectangle(
            [pad + 3, pad + 6, pad + box + 3, pad + box + 6], radius=radius, fill=(0, 0, 0, 120))
        shadow = shadow.filter(ImageFilter.GaussianBlur(8))
        canvas.alpha_composite(shadow)
        canvas.alpha_composite(rounded, (pad, pad))
        return ImageTk.PhotoImage(canvas)
    except Exception:
        return None


def format_duration(seconds: float) -> str:
    seconds = int(seconds or 0)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    if h:
        return f"{h} godz. {m} min"
    if m:
        return f"{m} min {s} s"
    return f"{s} s"


def format_size(num_bytes: int) -> str:
    n = float(num_bytes or 0)
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return f"{n:.1f} {unit}" if unit != "B" else f"{int(n)} B"
        n /= 1024
    return f"{n:.1f} TB"


def compute_library_stats(files: list) -> dict:
    """Łączny rozmiar i czas trwania folderu (odczyt przez mutagen, format-agnostyczny)."""
    total_size = 0
    total_dur = 0.0
    for f in files:
        try:
            total_size += os.path.getsize(f)
        except Exception:
            pass
        try:
            audio = mutagen.File(f)
            if audio is not None and getattr(audio, "info", None) is not None:
                total_dur += float(getattr(audio.info, "length", 0) or 0)
        except Exception:
            pass
    return {"size": total_size, "duration": total_dur}


# ── Historia ostatnio otwieranych folderów ─────────────────────────────────

def _history_path() -> Path:
    return _resource_dir() / "audiotagai_historia.json"

def load_history() -> list:
    try:
        p = _history_path()
        if not p.exists():
            return []
        data = json.loads(p.read_text(encoding="utf-8"))
        return [d for d in data if isinstance(d, str)][:12]
    except Exception:
        return []

def save_history(history: list):
    try:
        _history_path().write_text(json.dumps(history[:12], ensure_ascii=False, indent=0), encoding="utf-8")
    except Exception:
        pass

def add_to_history(folder: str):
    hist = [h for h in load_history() if h != folder]
    hist.insert(0, folder)
    save_history(hist[:12])


# ═══════════════════════════════════════════════════════════════════════════
#  NOWOCZESNE WIDGETY — zaokrąglone, "wypukłe" przyciski i przełączniki
#  rysowane na Canvas (Tkinter/ttk nie wspiera zaokrąglonych rogów natywnie).
#  Czysto wizualne dodatki — logika programu (search_*/write_tags/…) powyżej
#  pozostaje nietknięta.
# ═══════════════════════════════════════════════════════════════════════════

def _shade(hexcolor: str, amount: float) -> str:
    """Rozjaśnia (amount > 0) albo przyciemnia (amount < 0) kolor #RRGGBB."""
    try:
        h = hexcolor.lstrip("#")
        r, g, b = int(h[0:2], 16), int(h[2:4], 16), int(h[4:6], 16)
        if amount >= 0:
            r = int(r + (255 - r) * amount); g = int(g + (255 - g) * amount); b = int(b + (255 - b) * amount)
        else:
            r = int(r * (1 + amount)); g = int(g * (1 + amount)); b = int(b * (1 + amount))
        r, g, b = max(0, min(255, r)), max(0, min(255, g)), max(0, min(255, b))
        return f"#{r:02x}{g:02x}{b:02x}"
    except Exception:
        return hexcolor


def _rounded_points(x1, y1, x2, y2, r):
    r = max(1, min(r, (x2 - x1) / 2, (y2 - y1) / 2))
    return [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2,
            x2 - r, y2, x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]


def draw_rounded_rect(canvas: tk.Canvas, x1, y1, x2, y2, r, **kw):
    return canvas.create_polygon(_rounded_points(x1, y1, x2, y2, r), smooth=True, **kw)


class ModernButton(tk.Canvas):
    """Zaokrąglony, 'wypukły' przycisk z efektem hover/press — zamiennik ttk.Button."""

    _PALETTES = {
        "primary": (ACC,      "#8f80f9", "#6355d4", "white"),
        "success": ("#059669", "#10b981", "#047857", "white"),
        "danger":  ("#dc2626", "#ef4444", "#b91c1c", "white"),
        "outline": (CARD,      BORDER,    PANEL,     TEXT),
        "ghost":   (PANEL,     CARD,      BORDER,    TEXT),
    }

    def __init__(self, parent, text="", command=None, kind="primary", bg=None,
                 width=None, height=38, radius=11, font=("Segoe UI", 10, "bold"),
                 padx=16, state="normal"):
        self._base, self._hover, self._press, self._fg = self._PALETTES.get(kind, self._PALETTES["primary"])
        parent_bg = bg
        if parent_bg is None:
            try:
                parent_bg = parent["bg"]
            except Exception:
                parent_bg = BG
        if width is None:
            try:
                width = tkfont.Font(font=font).measure(text) + padx * 2
            except Exception:
                width = int(len(text) * 7.3) + padx * 2
            width = max(64, width)
        super().__init__(parent, width=width, height=height, bg=parent_bg,
                          highlightthickness=0, bd=0)
        self.text, self.radius, self.font = text, radius, font
        self._state = state
        self.command = command
        self._cur_w, self._cur_h = width, height
        self._last_key = "base"
        self._redraw("base")
        self.bind("<Enter>", lambda e: self._redraw("hover"))
        self.bind("<Leave>", lambda e: self._redraw("base"))
        self.bind("<ButtonPress-1>", lambda e: self._redraw("press"))
        self.bind("<ButtonRelease-1>", self._on_release)
        self.bind("<Configure>", self._on_configure)
        self._update_cursor()

    def _on_configure(self, event):
        # widget mógł zostać rozciągnięty przez pack(fill="x") — narysuj na nowo w realnym rozmiarze
        if event.width > 1 and event.height > 1:
            self._cur_w, self._cur_h = event.width, event.height
            self._redraw(self._last_key)

    def _update_cursor(self):
        try:
            self.configure(cursor="hand2" if self._state == "normal" else "arrow")
        except Exception:
            pass

    def _redraw(self, key):
        if self._state != "normal":
            key = "base"
        self._last_key = key
        self.delete("all")
        w, h = self._cur_w, self._cur_h
        color = {"base": self._base, "hover": self._hover, "press": self._press}[key]
        if self._state == "disabled":
            color, fg = BORDER, MUTED
        else:
            fg = self._fg
        lift = 0 if key == "press" else 2
        # cień pod przyciskiem — daje wrażenie uniesienia nad tłem
        if self._state == "normal" and lift:
            draw_rounded_rect(self, 2, 4, w - 2, h, self.radius, fill=_shade(str(self["bg"]), -0.35), outline="")
        y2 = h - lift
        draw_rounded_rect(self, 0, 0, w, y2, self.radius, fill=color, outline="")
        if self._state == "normal" and key != "press":
            # jaśniejszy górny pasek = efekt 'wypukłości' / połysku
            draw_rounded_rect(self, 2, 2, w - 2, max(6, y2 * 0.5), max(2, self.radius - 4),
                               fill=_shade(color, 0.16), outline="")
        self.create_text(w / 2, y2 / 2, text=self.text, fill=fg, font=self.font)

    def _on_release(self, e):
        if self._state != "normal":
            return
        inside = 0 <= e.x <= self._cur_w and 0 <= e.y <= self._cur_h
        self._redraw("hover" if inside else "base")
        if inside and self.command:
            self.command()

    def configure(self, **kw):
        if "state" in kw:
            self._state = kw.pop("state")
            self._update_cursor()
            self._redraw("base")
        if "text" in kw:
            self.text = kw.pop("text")
            self._redraw("base")
        if kw:
            super().configure(**kw)
    config = configure

    def cget_state(self):
        return self._state


class ModernToggle(tk.Canvas):
    """Nowoczesny przełącznik (pigułka) — zamiennik Checkbutton, zwraca .var (tk.BooleanVar)."""

    def __init__(self, parent, text="", color=ACC, bg=None, value=True, command=None, font=("Segoe UI", 8)):
        parent_bg = bg
        if parent_bg is None:
            try:
                parent_bg = parent["bg"]
            except Exception:
                parent_bg = BG
        self._sw, self._sh = 34, 18
        self.text, self.color, self.font = text, color, font
        est_w = self._sw + 10 + int(len(text) * 6.4) + 4
        super().__init__(parent, width=est_w, height=22, bg=parent_bg, highlightthickness=0, bd=0, cursor="hand2")
        self.var = tk.BooleanVar(value=value)
        self.command = command
        self._draw()
        self.bind("<Button-1>", self._toggle)

    def _draw(self):
        self.delete("all")
        on = self.var.get()
        track = self.color if on else BORDER
        draw_rounded_rect(self, 0, 2, self._sw, self._sh + 2, (self._sh) / 2, fill=track, outline="")
        knob_x = self._sw - 9 if on else 9
        self.create_oval(knob_x - 7, 3, knob_x + 7, 17, fill="white", outline="")
        self.create_text(self._sw + 8, 11, text=self.text, anchor="w", fill=TEXT, font=self.font)

    def _toggle(self, event=None):
        self.var.set(not self.var.get())
        self._draw()
        if self.command:
            self.command(self.var.get())

    def get(self):
        return self.var.get()

    def set(self, value):
        self.var.set(bool(value))
        self._draw()


class RoundedCard(tk.Frame):
    """Karta z zaokrąglonymi rogami — canvas z tłem + osadzona ramka na zawartość (.inner)."""

    def __init__(self, parent, bg_color=CARD, parent_bg=None, radius=14, **kw):
        pbg = parent_bg
        if pbg is None:
            try:
                pbg = parent["bg"]
            except Exception:
                pbg = BG
        super().__init__(parent, bg=pbg, **kw)
        self._canvas = tk.Canvas(self, bg=pbg, highlightthickness=0, bd=0)
        self._canvas.pack(fill="both", expand=True)
        self.inner = tk.Frame(self._canvas, bg=bg_color)
        self._win = self._canvas.create_window(0, 0, window=self.inner, anchor="nw")
        self._bg_color, self._radius = bg_color, radius
        self._canvas.bind("<Configure>", self._redraw)

    def _redraw(self, event=None):
        w = self._canvas.winfo_width(); h = self._canvas.winfo_height()
        if w < 2 or h < 2:
            return
        self._canvas.delete("bg")
        draw_rounded_rect(self._canvas, 0, 0, w, h, self._radius, fill=self._bg_color, outline="", tags="bg")
        self._canvas.tag_lower("bg")
        self._canvas.coords(self._win, 0, 0)
        self._canvas.itemconfig(self._win, width=w, height=h)


class _TextVarAdapter:
    """Udaje interfejs get()/set() z tk.StringVar dla wielowierszowego tk.Text —
    dzięki temu pole 'opis' (długi tekst) może korzystać z tej samej generycznej
    pętli po self._ed co reszta pól (Tytuł, Autor…), bez zmian gdzie indziej w kodzie."""
    def __init__(self, text_widget: tk.Text):
        self._w = text_widget

    def get(self) -> str:
        return self._w.get("1.0", "end-1c")

    def set(self, value: str):
        self._w.delete("1.0", "end")
        if value:
            self._w.insert("1.0", value)


# ═══════════════════════════════════════════════════════════════════════════
#  GUI
# ═══════════════════════════════════════════════════════════════════════════

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("AudioTagAI")
        self.geometry("1220x860")
        self.minsize(920, 680)
        self.configure(bg=BG)

        self.folder_path    = ""
        self.audio_files    = []
        self.parsed_info    = {}
        self.search_results = []
        self.selected_idx   = -1
        self.cover_data     : Optional[bytes] = None
        self.cover_photo    = None
        self.log_q          = queue.Queue()
        self._ui_q          = queue.Queue()   # wywołania GUI zlecane z wątków roboczych
        self._writing       = False           # trwa zapis tagów (blokuje wczytanie innego folderu)
        self._load_gen      = 0
        self._busy          = False
        self._queue_items   = []   # kolejka wsadowa: [{"path":..., "status":..., "id":...}]
        self._queue_running = False
        self._queue_stop    = False

        self._apply_icon()
        self._style()
        self._ui()
        self.after(80, self._flush_log)
        self.after(120, self._refresh_history_ui)

        # skróty klawiszowe
        self.bind("<Control-o>", lambda e: self._browse())
        self.bind("<F5>", lambda e: self._search())

        for line, tag in [
            ("╔══════════════════════════════════════╗", "acc"),
            ("║  AudioTagAI v5 Premium — PL audio 🎧  ║", "acc"),
            ("╚══════════════════════════════════════╝", "acc"),
            ("Kliknij  📁 Otwórz folder  aby zacząć   ", "dim"),
        ]:
            self._log(line, tag)
        if LOG_FILE:
            self._log(f"Plik dziennika: {LOG_FILE}", "dim")

    def report_callback_exception(self, exc, val, tb):
        """Błędy w interfejsie Tk — zamiast znikać bez śladu, trafiają do dziennika."""
        _flog.error("Błąd interfejsu", exc_info=(exc, val, tb))
        self._log(f"✗ Błąd interfejsu: {val}", "err")

    def _apply_icon(self):
        try:
            ico = get_or_create_icon_path()
            if ico and ico.exists():
                self.iconbitmap(default=str(ico))
        except Exception:
            pass

    # ── Style ─────────────────────────────────────────────────────────────

    def _style(self):
        s = ttk.Style(self); s.theme_use("clam")
        base = dict(background=BG, foreground=TEXT, font=("Segoe UI", 10), borderwidth=0)
        s.configure(".", **base)
        s.configure("TFrame",       background=BG)
        s.configure("TLabel",       background=BG,   foreground=TEXT)
        s.configure("TButton",      background=ACC,   foreground="white",
                    borderwidth=0, font=("Segoe UI", 10, "bold"), padding=(14, 8))
        s.map("TButton", background=[("active", "#6355d4"), ("disabled", BORDER)],
              foreground=[("disabled", MUTED)])
        s.configure("Out.TButton",  background=CARD, foreground=TEXT,
                    borderwidth=1, relief="solid", padding=(12, 7), font=("Segoe UI", 10))
        s.map("Out.TButton", background=[("active", BORDER)])
        s.configure("Go.TButton",   background="#059669", foreground="white",
                    borderwidth=0, font=("Segoe UI", 11, "bold"), padding=(18, 10))
        s.map("Go.TButton",  background=[("active", "#047857"), ("disabled", BORDER)])
        s.configure("TEntry",       fieldbackground=CARD, background=CARD,
                    foreground=TEXT, insertcolor=TEXT, borderwidth=1,
                    relief="solid", padding=(8, 6))
        s.configure("TProgressbar", troughcolor=BORDER, background=ACC, thickness=5, borderwidth=0)
        s.configure("Treeview",         background=CARD, foreground=TEXT,
                    fieldbackground=CARD, borderwidth=0, rowheight=30, font=("Segoe UI", 9))
        s.configure("Treeview.Heading", background=PANEL, foreground=MUTED,
                    font=("Segoe UI", 9, "bold"), borderwidth=0, relief="flat")
        s.map("Treeview", background=[("selected", ACC)], foreground=[("selected", "white")])
        s.configure("TScrollbar",  background=BORDER, troughcolor=BG,
                    arrowcolor=MUTED, borderwidth=0, width=10)
        s.configure("TNotebook",     background=BG, borderwidth=0)
        s.configure("TNotebook.Tab", background=PANEL, foreground=MUTED,
                    padding=(16, 8), font=("Segoe UI", 10))
        s.map("TNotebook.Tab", background=[("selected", CARD)], foreground=[("selected", TEXT)])

    # ── Build UI ──────────────────────────────────────────────────────────

    def _ui(self):
        top = tk.Frame(self, bg=PANEL, height=60)
        top.pack(fill="x"); top.pack_propagate(False)

        badge_holder = tk.Frame(top, bg=PANEL)
        badge_holder.pack(side="left", padx=(16, 10), pady=10)
        try:
            self._logo_img = ImageTk.PhotoImage(generate_icon_image(72).resize((36, 36), Image.LANCZOS))
            tk.Label(badge_holder, image=self._logo_img, bg=PANEL).pack()
        except Exception:
            tk.Label(badge_holder, text="🎧", bg=PANEL, fg=TEXT, font=("Segoe UI", 18)).pack()

        title_holder = tk.Frame(top, bg=PANEL)
        title_holder.pack(side="left", pady=8)
        row1 = tk.Frame(title_holder, bg=PANEL); row1.pack(anchor="w")
        tk.Label(row1, text="AudioTagAI", bg=PANEL, fg=TEXT,
                 font=("Segoe UI", 15, "bold")).pack(side="left")
        _pill(row1, "PREMIUM", ACC2)
        tk.Label(title_holder, text="Polskie audiobooki i muzyka  ·  Lubimyczytac · Audioteka · Empik · Google Books",
                 bg=PANEL, fg=MUTED, font=("Segoe UI", 8)).pack(anchor="w")

        right_holder = tk.Frame(top, bg=PANEL)
        right_holder.pack(side="right", padx=16)
        ModernButton(right_holder, text="ℹ  O programie", kind="ghost", bg=PANEL,
                     command=self._show_about, height=34).pack(side="right")
        self._busy_lbl = tk.Label(right_holder, text="", bg=PANEL, fg=AMBER, font=("Segoe UI", 9))
        self._busy_lbl.pack(side="right", padx=12)

        # cienki pasek gradientowy pod nagłówkiem — akcent premium
        grad = tk.Canvas(self, height=3, bg=BG, highlightthickness=0)
        grad.pack(fill="x")
        self._draw_gradient_bar(grad)
        tk.Frame(self, bg=BORDER, height=1).pack(fill="x")

        self._toast_lbl = tk.Label(self, text="", font=("Segoe UI", 9, "bold"),
                                    anchor="w", padx=16, pady=7)
        # (celowo niedołączony do layoutu — pojawia się/znika przez _toast())

        content = tk.Frame(self, bg=BG)
        content.pack(fill="both", expand=True)
        self._content_frame = content
        left_outer = tk.Frame(content, bg=BG, width=355)
        left_outer.pack(side="left", fill="y"); left_outer.pack_propagate(False)

        # boczny panel przewijany (Canvas + Scrollbar) — gwarantuje, że wszystkie opcje
        # są zawsze dostępne, nawet gdy okno jest niższe lub dojdzie więcej źródeł
        left_canvas = tk.Canvas(left_outer, bg=BG, highlightthickness=0, bd=0)
        left_scroll = ttk.Scrollbar(left_outer, orient="vertical", command=left_canvas.yview)
        left_canvas.configure(yscrollcommand=left_scroll.set)
        left_canvas.pack(side="left", fill="both", expand=True)
        left_scroll.pack(side="right", fill="y")

        left = tk.Frame(left_canvas, bg=BG)
        left_win = left_canvas.create_window((0, 0), window=left, anchor="nw")

        def _left_on_configure(event=None):
            left_canvas.configure(scrollregion=left_canvas.bbox("all"))
        left.bind("<Configure>", _left_on_configure)

        def _left_canvas_configure(event):
            left_canvas.itemconfig(left_win, width=event.width)
        left_canvas.bind("<Configure>", _left_canvas_configure)

        def _left_wheel(event):
            left_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        def _left_bind_wheel(event=None):
            left_canvas.bind_all("<MouseWheel>", _left_wheel)
        def _left_unbind_wheel(event=None):
            left_canvas.unbind_all("<MouseWheel>")
        left_canvas.bind("<Enter>", _left_bind_wheel)
        left_canvas.bind("<Leave>", _left_unbind_wheel)

        tk.Frame(content, bg=BORDER, width=1).pack(side="left", fill="y")
        right = tk.Frame(content, bg=BG)
        right.pack(side="left", fill="both", expand=True)
        self._sidebar(left)
        self._main(right)

        tk.Frame(self, bg=BORDER, height=1).pack(fill="x", side="bottom")
        bot = tk.Frame(self, bg=PANEL, height=44)
        bot.pack(fill="x", side="bottom"); bot.pack_propagate(False)
        self._pv = tk.DoubleVar()
        ttk.Progressbar(bot, variable=self._pv, maximum=100).pack(fill="x", padx=16, pady=(10, 2))
        tk.Label(bot, text=f"© {time.strftime('%Y')} Andrzej Małek  ·  AudioTagAI {APP_VERSION}",
                 bg=PANEL, fg=MUTED, font=("Segoe UI", 7)).pack(anchor="w", padx=16)

    def _draw_gradient_bar(self, canvas: tk.Canvas):
        def redraw(event=None):
            canvas.delete("all")
            w = canvas.winfo_width() or self.winfo_width() or 1220
            c1, c2 = (0x7c, 0x6a, 0xf7), (0x5e, 0xea, 0xd4)
            steps = max(1, w // 4)
            for i in range(steps):
                t = i / max(1, steps - 1)
                r = int(c1[0] + (c2[0] - c1[0]) * t)
                g = int(c1[1] + (c2[1] - c1[1]) * t)
                b = int(c1[2] + (c2[2] - c1[2]) * t)
                x = int(i * w / steps)
                canvas.create_rectangle(x, 0, x + w // steps + 1, 3, fill=f"#{r:02x}{g:02x}{b:02x}", width=0)
        canvas.bind("<Configure>", redraw)
        self.after(50, redraw)

    def _show_about(self):
        win = tk.Toplevel(self)
        win.title("O programie")
        win.configure(bg=BG)
        win.geometry("420x400")
        win.resizable(False, False)
        try:
            ico = get_or_create_icon_path()
            if ico: win.iconbitmap(default=str(ico))
        except Exception:
            pass
        try:
            logo = ImageTk.PhotoImage(generate_icon_image(96).resize((64, 64), Image.LANCZOS))
            lbl = tk.Label(win, image=logo, bg=BG); lbl.image = logo
            lbl.pack(pady=(20, 8))
        except Exception:
            tk.Label(win, text="🎧", bg=BG, fg=TEXT, font=("Segoe UI", 32)).pack(pady=(20, 8))
        tk.Label(win, text="AudioTagAI", bg=BG, fg=TEXT, font=("Segoe UI", 16, "bold")).pack()
        tk.Label(win, text=APP_VERSION, bg=BG, fg=ACC2, font=("Segoe UI", 10, "bold")).pack(pady=(0, 10))
        tk.Label(win, text="Automatyczny tagger polskich audiobooków i muzyki.\n"
                            "Rozpoznaje autora, tytuł i lektora z nazwy folderu,\n"
                            "pobiera okładkę i uzupełnia metadane pod Plex.",
                 bg=BG, fg=MUTED, font=("Segoe UI", 9), justify="center").pack(pady=(0, 14))
        tk.Frame(win, bg=BORDER, height=1).pack(fill="x", padx=30)
        tk.Label(win, text=f"© {time.strftime('%Y')} Andrzej Małek", bg=BG, fg=TEXT,
                 font=("Segoe UI", 9, "bold")).pack(pady=(14, 2))
        tk.Label(win, text="Wszelkie prawa zastrzeżone.", bg=BG, fg=MUTED, font=("Segoe UI", 8)).pack()
        ModernButton(win, text="Zamknij", kind="outline", bg=BG, command=win.destroy, width=140).pack(pady=16)

    def _sidebar(self, p):
        P = dict(padx=14)

        _lbl(p, "FOLDER")
        row = tk.Frame(p, bg=BG); row.pack(fill="x", padx=14, pady=(0, 6))
        self._fldr = tk.Label(row, text="Nie wybrano folderu",
            bg=CARD, fg=MUTED, font=("Segoe UI", 8), anchor="w",
            wraplength=308, justify="left", padx=8, pady=6)
        self._fldr.pack(fill="x", pady=(0, 6))
        ModernButton(row, text="📁  Otwórz folder z plikami audio", kind="primary", bg=BG,
                     command=self._browse, height=40).pack(fill="x")
        self._flbl = tk.Label(p, text="", bg=BG, fg=MUTED, font=("Segoe UI", 8), anchor="w")
        self._flbl.pack(anchor="w", padx=14, pady=(2, 0))
        self._stats_lbl = tk.Label(p, text="", bg=BG, fg=ACC2, font=("Segoe UI", 8, "bold"), anchor="w")
        self._stats_lbl.pack(anchor="w", padx=14, pady=(2, 0))

        hist_row = tk.Frame(p, bg=BG); hist_row.pack(fill="x", padx=14, pady=(6, 0))
        tk.Label(hist_row, text="Ostatnie:", bg=BG, fg=MUTED, font=("Segoe UI", 8)).pack(side="left")
        self._hist_var = tk.StringVar()
        self._hist_combo = ttk.Combobox(hist_row, textvariable=self._hist_var, state="readonly",
                                         font=("Segoe UI", 8), values=[])
        self._hist_combo.pack(side="left", fill="x", expand=True, padx=(6, 0))
        self._hist_combo.bind("<<ComboboxSelected>>", self._on_history_pick)
        self._hist_map = {}

        _sep(p)
        _lbl(p, "ROZPOZNANO Z NAZWY FOLDERU")
        card_wrap = RoundedCard(p, bg_color=CARD, parent_bg=BG, radius=14)
        card_wrap.pack(fill="x", padx=14)
        card = card_wrap.inner
        tk.Frame(card, bg=CARD, height=8).pack()
        self._ia = _irow(card, "Autor:")
        self._it = _irow(card, "Tytuł:")
        self._in = _irow(card, "Lektor:")
        self._iy = _irow(card, "Typ:")
        tk.Frame(card, bg=CARD, height=8).pack()

        _sep(p)
        _lbl(p, "ZAPYTANIE WYSZUKIWANIA")
        tk.Label(p, text="Możesz edytować przed wyszukaniem:",
                 bg=BG, fg=MUTED, font=("Segoe UI", 8)).pack(anchor="w", padx=14)
        self._qv = tk.StringVar()
        qentry = ttk.Entry(p, textvariable=self._qv, font=("Segoe UI", 9))
        qentry.pack(fill="x", padx=14, pady=(2, 6))
        qentry.bind("<Return>", lambda e: self._search())

        _lbl(p, "ŹRÓDŁA (polskie priorytet)")
        def _src_row():
            r = tk.Frame(p, bg=BG); r.pack(fill="x", padx=14, pady=(0, 4)); return r
        row_a = _src_row()
        self._s_lc  = ModernToggle(row_a, "Lubimyczytac", GREEN, bg=BG); self._s_lc.pack(side="left", padx=(0, 10))
        self._s_at  = ModernToggle(row_a, "Audioteka",    ACC2,  bg=BG); self._s_at.pack(side="left")
        row_b = _src_row()
        self._s_em  = ModernToggle(row_b, "Empik",        AMBER, bg=BG); self._s_em.pack(side="left", padx=(0, 10))
        self._s_gb  = ModernToggle(row_b, "Google Books PL", ACC, bg=BG); self._s_gb.pack(side="left")
        row_c = _src_row()
        self._s_ol  = ModernToggle(row_c, "Open Library",  MUTED, bg=BG); self._s_ol.pack(side="left", padx=(0, 10))
        self._s_it  = ModernToggle(row_c, "iTunes",        RED,   bg=BG); self._s_it.pack(side="left")
        row_d = _src_row()
        self._s_wiki = ModernToggle(row_d, "Wikipedia PL", ACC2,  bg=BG); self._s_wiki.pack(side="left", padx=(0, 10))
        self._s_nx   = ModernToggle(row_d, "Nexto",        ACC,   bg=BG, value=False)
        self._s_nx.pack(side="left")
        row_e = _src_row()
        self._s_tk   = ModernToggle(row_e, "TaniaKsiazka", GREEN, bg=BG, value=False)
        self._s_tk.pack(side="left")
        tk.Label(p, text="Nexto / TaniaKsiazka: eksperymentalne, mogą nie zwracać wyników",
                 bg=BG, fg=MUTED, font=("Segoe UI", 7), wraplength=320, justify="left",
                 anchor="w").pack(anchor="w", padx=14, pady=(0, 4))

        ModernButton(p, text="🔍  Szukaj metadanych", kind="outline", bg=BG,
                     command=self._search, height=40).pack(fill="x", **P)

        _sep(p)
        _lbl(p, "PRZY ZAPISIE TAGÓW")
        opt = tk.Frame(p, bg=BG); opt.pack(fill="x", padx=14, pady=(0, 8))
        self._s_rename = ModernToggle(opt, "Ponumeruj pliki 01, 02, 03…", ACC2, bg=BG, value=True)
        self._s_rename.pack(side="left")
        opt2 = tk.Frame(p, bg=BG); opt2.pack(fill="x", padx=14, pady=(0, 8))
        self._s_savecover = ModernToggle(opt2, "Zapisz cover.jpg w folderze", ACC2, bg=BG, value=True)
        self._s_savecover.pack(side="left")

        _sep(p)
        _lbl(p, "DZIENNIK")
        ModernButton(p, text="📄  Otwórz plik dziennika", kind="outline", bg=BG,
                     command=self._open_log_file, height=32).pack(fill="x", padx=14, pady=(0, 6))
        wrap = tk.Frame(p, bg=CARD, bd=1, relief="solid")
        wrap.pack(fill="both", expand=True, padx=14, pady=(0, 12))
        self._log_box = tk.Text(wrap, bg=CARD, fg=MUTED, font=("Consolas", 8),
                                 wrap="word", state="disabled", relief="flat",
                                 insertbackground=TEXT, highlightthickness=0)
        sb = ttk.Scrollbar(wrap, orient="vertical", command=self._log_box.yview)
        self._log_box.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self._log_box.pack(fill="both", expand=True, padx=4, pady=4)
        for t, c in [("ok", GREEN), ("err", RED), ("acc", ACC2), ("dim", MUTED), ("amb", AMBER)]:
            self._log_box.tag_config(t, foreground=c)

    def _main(self, p):
        nb = ttk.Notebook(p)
        nb.pack(fill="both", expand=True, padx=8, pady=8)

        t1 = tk.Frame(nb, bg=BG)
        nb.add(t1, text="  Wyniki wyszukiwania  ")

        top = tk.Frame(t1, bg=BG)
        top.pack(fill="x", padx=12, pady=12)

        cbox = tk.Frame(top, bg=BG, width=200, height=200)
        cbox.pack(side="left", padx=(0, 16)); cbox.pack_propagate(False)
        self._covlbl = tk.Label(cbox, bg=BG, fg=MUTED,
                                 text="okładka\nbrak", font=("Segoe UI", 9))
        self._covlbl.pack(expand=True)

        inf = tk.Frame(top, bg=BG)
        inf.pack(side="left", fill="both", expand=True)
        self._stitle  = tk.Label(inf, text="← Wybierz wynik z listy",
            bg=BG, fg=TEXT, font=("Segoe UI", 14, "bold"),
            wraplength=520, justify="left", anchor="w")
        self._stitle.pack(anchor="w")
        self._sauthor = tk.Label(inf, text="", bg=BG, fg=ACC,
                                  font=("Segoe UI", 11), anchor="w")
        self._sauthor.pack(anchor="w")
        self._smeta   = tk.Label(inf, text="", bg=BG, fg=MUTED,
                                  font=("Segoe UI", 9), anchor="w")
        self._smeta.pack(anchor="w", pady=(2, 8))

        br = tk.Frame(inf, bg=BG); br.pack(anchor="w")
        ModernButton(br, text="⬇  Pobierz okładkę", kind="outline", bg=BG,
                     command=self._fetch_cover).pack(side="left", padx=(0, 10), pady=(0, 6))

        ModernButton(br, text="🖼  Dodaj ręcznie", kind="outline", bg=BG,
                     command=self._pick_cover_manually).pack(side="left", pady=(0, 6))

        br2 = tk.Frame(inf, bg=BG); br2.pack(anchor="w")
        ModernButton(br2, text="💾  Zapisz okładkę do folderu", kind="outline", bg=BG,
                     command=self._save_cover_to_folder).pack(side="left")

        ModernButton(inf,
            text="✅  ZAPISZ TAGI DO WSZYSTKICH PLIKÓW",
            kind="success", bg=BG, height=44, font=("Segoe UI", 11, "bold"),
            command=self._apply).pack(anchor="w", pady=(10, 0))

        tw = tk.Frame(t1, bg=BG)
        tw.pack(fill="both", expand=True, padx=12, pady=(0, 8))
        cols = [("title", 240, "Tytuł"), ("author", 165, "Autor"), ("year", 52, "Rok"),
                ("genre", 110, "Gatunek"), ("publisher", 110, "Wydawca"), ("source", 100, "Źródło")]
        self._tree = ttk.Treeview(tw, columns=[c[0] for c in cols],
                                   show="headings", selectmode="browse")
        for col, w, lbl in cols:
            self._tree.heading(col, text=lbl); self._tree.column(col, width=w, minwidth=40)
        vsb = ttk.Scrollbar(tw, orient="v", command=self._tree.yview)
        self._tree.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")
        self._tree.pack(fill="both", expand=True)
        self._tree.bind("<<TreeviewSelect>>", self._on_sel)

        t2 = tk.Frame(nb, bg=BG)
        nb.add(t2, text="  Lista plików  ")
        fw = tk.Frame(t2, bg=BG); fw.pack(fill="both", expand=True, padx=10, pady=10)
        self._ftree = ttk.Treeview(fw, columns=("n", "name", "status"), show="headings")
        self._ftree.heading("n",      text="#");       self._ftree.column("n",      width=45)
        self._ftree.heading("name",   text="Plik");    self._ftree.column("name",   width=530)
        self._ftree.heading("status", text="Status");  self._ftree.column("status", width=130)
        fvsb = ttk.Scrollbar(fw, orient="v", command=self._ftree.yview)
        self._ftree.configure(yscrollcommand=fvsb.set)
        fvsb.pack(side="right", fill="y"); self._ftree.pack(fill="both", expand=True)

        t3 = tk.Frame(nb, bg=BG); nb.add(t3, text="  Edycja ręczna  ")
        self._edit_tab(t3)

        t4 = tk.Frame(nb, bg=BG); nb.add(t4, text="  🚀 Kolejka (wsadowo)  ")
        self._queue_tab(t4)

    def _queue_tab(self, p):
        intro = tk.Frame(p, bg=BG); intro.pack(fill="x", padx=12, pady=(14, 4))
        tk.Label(intro, text="Przetwarzaj wiele audiobooków naraz — bez klikania każdego z osobna",
                 bg=BG, fg=TEXT, font=("Segoe UI", 12, "bold")).pack(anchor="w")
        tk.Label(intro, text="Dla każdego folderu: rozpozna autora/tytuł/lektora, znajdzie najlepszy wynik,\n"
                              "pobierze okładkę, zapisze tagi i ponumeruje pliki — automatycznie.",
                 bg=BG, fg=MUTED, font=("Segoe UI", 8), justify="left").pack(anchor="w", pady=(2, 0))

        top = tk.Frame(p, bg=BG); top.pack(fill="x", padx=12, pady=12)
        ModernButton(top, text="📁  Dodaj folder", kind="outline", bg=BG,
                     command=self._queue_add_folder).pack(side="left", padx=(0, 8))
        ModernButton(top, text="📚  Dodaj wszystkie podfoldery z…", kind="outline", bg=BG,
                     command=self._queue_add_subfolders).pack(side="left", padx=(0, 8))
        ModernButton(top, text="🗑  Usuń zaznaczone", kind="outline", bg=BG,
                     command=self._queue_remove_selected).pack(side="left", padx=(0, 8))

        tw = tk.Frame(p, bg=BG); tw.pack(fill="both", expand=True, padx=12, pady=(0, 8))
        cols = [("n", 40, "#"), ("folder", 320, "Folder"), ("info", 260, "Rozpoznano"), ("status", 220, "Status")]
        self._qtree = ttk.Treeview(tw, columns=[c[0] for c in cols], show="headings", selectmode="extended")
        for col, w, lbl in cols:
            self._qtree.heading(col, text=lbl); self._qtree.column(col, width=w, minwidth=40)
        qvsb = ttk.Scrollbar(tw, orient="v", command=self._qtree.yview)
        self._qtree.configure(yscrollcommand=qvsb.set)
        qvsb.pack(side="right", fill="y"); self._qtree.pack(fill="both", expand=True)

        bottom = tk.Frame(p, bg=BG); bottom.pack(fill="x", padx=12, pady=(0, 16))
        self._queue_start_btn = ModernButton(bottom, text="▶  Przetwórz całą kolejkę automatycznie",
                                              kind="success", bg=BG, height=42,
                                              command=self._queue_start)
        self._queue_start_btn.pack(side="left")
        self._queue_stop_btn = ModernButton(bottom, text="⏹  Zatrzymaj", kind="danger", bg=BG,
                                             height=42, command=self._queue_stop_now, state="disabled")
        self._queue_stop_btn.pack(side="left", padx=(10, 0))
        tk.Label(bottom, text="Korzysta z tych samych źródeł i opcji, co po lewej stronie.",
                 bg=BG, fg=MUTED, font=("Segoe UI", 8)).pack(side="left", padx=14)

    # ── Kolejka wsadowa ──────────────────────────────────────────────────

    def _queue_add_folder(self):
        folder = filedialog.askdirectory(title="Dodaj folder do kolejki")
        if folder:
            self._queue_add_one(folder)

    def _queue_add_subfolders(self):
        parent = filedialog.askdirectory(title="Wybierz folder nadrzędny (doda WSZYSTKIE jego podfoldery)")
        if not parent:
            return
        try:
            subs = sorted([str(d) for d in Path(parent).iterdir() if d.is_dir()])
        except Exception as e:
            messagebox.showerror("Błąd", str(e)); return
        added = 0
        for d in subs:
            try:
                if get_audio_files(d):
                    self._queue_add_one(d)
                    added += 1
            except Exception:
                pass
        if added == 0:
            messagebox.showinfo("Brak audiobooków", "Żaden podfolder nie zawiera plików audio.")
        else:
            self._log(f"📚 Dodano {added} folderów do kolejki z: {Path(parent).name}", "acc")

    def _queue_add_one(self, folder):
        qid = str(len(self._queue_items) + 1)
        name = Path(folder).name
        info = parse_folder(name)
        desc = f"{info.get('author', '') or '?'} — {info.get('title', '') or name}"
        item = {"id": qid, "path": folder, "status": "Oczekuje"}
        self._queue_items.append(item)
        self._qtree.insert("", "end", iid=qid, values=(qid, name, desc, "Oczekuje"))

    def _queue_remove_selected(self):
        if self._queue_running:
            return
        sel = self._qtree.selection()
        if not sel:
            return
        self._qtree.delete(*sel)
        self._queue_items = [it for it in self._queue_items if it["id"] not in sel]

    def _queue_set_status(self, qid, status):
        self._ui_call(lambda: self._qtree.set(qid, "status", status) if self._qtree.exists(qid) else None)

    def _queue_start(self):
        if self._queue_running or not self._queue_items:
            return
        self._queue_stop = False
        self._queue_running = True
        self._queue_start_btn.config(state="disabled")
        self._queue_stop_btn.config(state="normal")
        self._set_busy("Przetwarzam kolejkę…")
        threading.Thread(target=self._queue_process_w, daemon=True).start()

    def _queue_stop_now(self):
        self._queue_stop = True
        self._log("⏹ Zatrzymuję kolejkę po zakończeniu bieżącego folderu…", "amb")

    def _search_all_sync(self, pi, timeout_per_source=14):
        """Odpytuje wszystkie włączone źródła równolegle i zwraca posortowaną listę wyników
        (wersja synchroniczna do użytku wewnątrz wątku kolejki — nie dotyka logiki zakładki 'Wyniki')."""
        variants = (pi.get("query_variants") or [pi.get("q_full", "")])[:3]
        sources = []
        if self._s_lc.get(): sources.append(search_lubimyczytac)
        if self._s_at.get(): sources.append(search_audioteka)
        if self._s_em.get(): sources.append(search_empik)
        if self._s_gb.get(): sources.append(lambda q: search_google_books(q, True))
        if self._s_ol.get(): sources.append(search_openlibrary)
        if self._s_it.get(): sources.append(search_itunes)
        if getattr(self, "_s_wiki", None) and self._s_wiki.get(): sources.append(search_wikipedia_pl)
        if getattr(self, "_s_nx", None) and self._s_nx.get(): sources.append(search_nexto)
        if getattr(self, "_s_tk", None) and self._s_tk.get(): sources.append(search_taniaksiazka)

        results, lock = [], threading.Lock()

        def run_one(fn):
            r = []
            for v in variants:
                try:
                    r = fn(v)
                except Exception:
                    r = []
                if r:
                    break
            with lock:
                results.extend(r)

        threads = [threading.Thread(target=run_one, args=(fn,), daemon=True) for fn in sources]
        for t in threads: t.start()
        for t in threads: t.join(timeout=timeout_per_source)
        try:
            results.sort(key=lambda x: score_result(x, pi), reverse=True)
        except Exception:
            pass
        return results

    def _queue_process_w(self):
        total = len(self._queue_items)
        done_ok = done_err = 0
        for idx, item in enumerate(self._queue_items, 1):
            if self._queue_stop:
                self._queue_set_status(item["id"], "⏹ Przerwano")
                continue
            folder = item["path"]
            self._queue_set_status(item["id"], "⏳ Szukam…")
            self._log("", "dim")
            self._log(f"[Kolejka {idx}/{total}] 📁 {Path(folder).name}", "acc")
            try:
                files = get_audio_files(folder)
                if not files:
                    self._queue_set_status(item["id"], "⚠ Brak plików audio")
                    continue

                info = parse_folder(Path(folder).name)
                results = self._search_all_sync(info)
                best = results[0] if results else {}
                self._log(f"   znaleziono {len(results)} wyników, biorę najlepszy: "
                          f"{best.get('title', '(brak)') if results else '—'}", "dim")

                cover_data = None
                # Dokładnie jeden plik graficzny w folderze = niemal na pewno oryginalna
                # okładka od tego, kto przygotował audiobooka — ufamy jej bardziej niż
                # czemukolwiek z internetu i NIE próbujemy jej nadpisywać wynikiem online.
                local_cover_path = find_local_cover_image(folder)
                if local_cover_path:
                    cover_data = load_image_as_jpeg_cover(local_cover_path)
                    if cover_data:
                        self._log(f"   🖼 Okładka z folderu: {Path(local_cover_path).name}", "ok")
                if not cover_data:
                    cover_url = best.get("cover_url", "")
                    if cover_url:
                        raw = download_cover(cover_url)
                        if raw:
                            try:
                                img = Image.open(BytesIO(raw)).convert("RGB")
                                buf = BytesIO(); img.save(buf, format="JPEG", quality=92)
                                cover_data = buf.getvalue()
                            except Exception:
                                cover_data = None

                tags = {}
                for k in ("title", "year", "genre", "publisher", "description"):
                    if best.get(k): tags[k] = best[k]
                r_author = (best.get("author") or "").strip()
                r_title  = (best.get("title") or "").strip()
                if r_author and r_author.lower() != r_title.lower():
                    tags["author"] = r_author
                for k in ("author", "title", "narrator"):
                    if info.get(k): tags[k] = info[k]
                if not tags.get("genre") and info.get("type") == "audiobook":
                    tags["genre"] = "Audiobook"
                if not tags.get("album"):
                    tags["album"] = tags.get("title", "")

                self._queue_set_status(item["id"], "💾 Zapisuję tagi…")

                if hasattr(self, "_s_rename") and self._s_rename.get():
                    plan = plan_renumber(files)
                    if any(o != n for o, n in plan):
                        try:
                            files = apply_renumber(plan)
                        except Exception as e:
                            # zmiany zostały cofnięte — tagujemy pliki pod starymi nazwami
                            self._log(f"   ⚠ Nie udało się ponumerować plików (cofnięto): {e}", "amb")

                if cover_data and hasattr(self, "_s_savecover") and self._s_savecover.get():
                    try:
                        with open(os.path.join(folder, "cover.jpg"), "wb") as f:
                            f.write(cover_data)
                    except Exception as e:
                        self._log(f"   ⚠ Nie zapisano cover.jpg: {e}", "amb")

                ok = err = 0
                tot = len(files)
                for i, path in enumerate(files, 1):
                    success, reason = write_tags(path, tags, cover_data, i, tot)
                    if success:
                        ok += 1
                    else:
                        err += 1
                        self._log(f"   ✗ {Path(path).name}  ({reason})", "err")

                if err == 0:
                    self._queue_set_status(item["id"], f"✅ Gotowe ({ok} plików)")
                    done_ok += 1
                else:
                    self._queue_set_status(item["id"], f"⚠ {ok} OK / {err} błędów")
                    done_err += 1
                self._log(f"   → {tags.get('author', '?')} — {tags.get('title', '?')}  "
                          f"({ok} OK, {err} błędów)", "ok" if err == 0 else "amb")
            except Exception as e:
                _flog.error("Błąd przetwarzania folderu %s", folder, exc_info=True)
                self._queue_set_status(item["id"], f"✗ Błąd: {e}")
                done_err += 1
                self._log(f"   ✗ Błąd przetwarzania: {e}", "err")

        self._queue_running = False
        self._ui_call(lambda: self._queue_start_btn.config(state="normal"))
        self._ui_call(lambda: self._queue_stop_btn.config(state="disabled"))
        self._ui_call(lambda: self._set_busy(""))
        self._log("", "dim")
        self._log(f"🏁 Kolejka zakończona: {done_ok} gotowych, {done_err} z błędem/pominiętych.", "acc")
        self._toast(f"🏁 Kolejka zakończona — {done_ok} książek gotowych do Plex",
                    "ok" if done_err == 0 else "amb")

    def _edit_tab(self, p):
        f = tk.Frame(p, bg=BG); f.pack(fill="both", expand=True, padx=22, pady=18)
        tk.Label(f, text="Ręczna edycja tagów", bg=BG, fg=TEXT,
                 font=("Segoe UI", 13, "bold")).pack(anchor="w", pady=(0, 4))
        tk.Label(f, text="Puste pola są pomijane — nadpiszą wyniki wyszukiwania.",
                 bg=BG, fg=MUTED, font=("Segoe UI", 8)).pack(anchor="w", pady=(0, 12))
        self._ed = {}
        for k, lbl in [
            ("title", "Tytuł / Nazwa albumu"), ("author", "Autor / Artysta"),
            ("album", "Album (jeśli inny niż tytuł)"), ("year", "Rok wydania"),
            ("genre", "Gatunek  (np. Audiobook, Kryminał, Thriller)"),
            ("narrator", "Lektor / Narrator"), ("publisher", "Wydawca"),
        ]:
            r = tk.Frame(f, bg=BG); r.pack(fill="x", pady=5)
            tk.Label(r, text=lbl, bg=BG, fg=MUTED, font=("Segoe UI", 9),
                     width=34, anchor="w").pack(side="left")
            v = tk.StringVar()
            ttk.Entry(r, textvariable=v, font=("Segoe UI", 9)).pack(
                side="left", fill="x", expand=True)
            self._ed[k] = v

        # Opis fabuły — pole wielowierszowe (pobierany automatycznie z Google Books /
        # Wikipedii gdy dostępny; można go tu też dopisać lub poprawić ręcznie)
        dr = tk.Frame(f, bg=BG); dr.pack(fill="x", pady=5)
        tk.Label(dr, text="Opis fabuły / streszczenie", bg=BG, fg=MUTED, font=("Segoe UI", 9),
                 width=34, anchor="nw").pack(side="left", anchor="n")
        desc_wrap = tk.Frame(dr, bg=CARD, highlightthickness=1, highlightbackground=BORDER)
        desc_wrap.pack(side="left", fill="both", expand=True)
        desc_text = tk.Text(desc_wrap, height=5, wrap="word", font=("Segoe UI", 9),
                             bg=CARD, fg=TEXT, insertbackground=TEXT, relief="flat",
                             padx=8, pady=6, bd=0, highlightthickness=0)
        desc_vsb = ttk.Scrollbar(desc_wrap, orient="v", command=desc_text.yview)
        desc_text.configure(yscrollcommand=desc_vsb.set)
        desc_vsb.pack(side="right", fill="y")
        desc_text.pack(side="left", fill="both", expand=True)
        self._ed["description"] = _TextVarAdapter(desc_text)

        tk.Frame(f, bg=BORDER, height=1).pack(fill="x", pady=14)
        r2 = tk.Frame(f, bg=BG); r2.pack(anchor="w")
        ModernButton(r2, text="✅  Zapisz ręczne tagi", kind="success", bg=BG, height=40,
                     command=self._apply_manual).pack(side="left", padx=(0, 10))
        ModernButton(r2, text="Wyczyść pola", kind="outline", bg=BG,
                     command=lambda: [v.set("") for v in self._ed.values()]).pack(side="left")

    # ── Akcje ─────────────────────────────────────────────────────────────

    def _browse(self):
        folder = filedialog.askdirectory(title="Wybierz folder z plikami audio")
        if folder: self._load(folder)

    def _load(self, folder):
        if self._writing:
            messagebox.showinfo("Trwa zapis",
                "Poczekaj, aż skończy się zapis tagów poprzedniego audiobooka\n"
                "(pasek postępu) — dopiero wtedy otwórz następny folder.")
            return
        self._load_gen += 1
        self.folder_path = folder
        try:
            rec = recover_tmp_files(folder)
        except Exception as e:
            rec = {}
            self._log(f"  ⚠ Błąd sprzątania plików tymczasowych: {e}", "amb")
        if rec.get("deleted"):
            self._log(f"🧹 Usunięto {len(rec['deleted'])} zbędnych plików *.__audiotagai_tmp__", "acc")
        if rec.get("restored"):
            self._log(f"♻ Przywrócono {len(rec['restored'])} plików z nazw tymczasowych", "acc")
        if rec.get("kept"):
            self._log(f"⚠ Pozostawiono {len(rec['kept'])} plików tymczasowych — sprawdź ręcznie", "amb")
        self.audio_files = get_audio_files(folder)

        # Wyczyść pola z POPRZEDNIEGO audiobooka — wcześniej rok, wydawca, gatunek,
        # opis, a nawet lektor zostawały z poprzedniej książki i trafiały do tagów
        # następnej (gdy nowa nie miała tych danych).
        for v in self._ed.values():
            v.set("")
        self.selected_idx = -1
        self.search_results = []
        total = len(self.audio_files)
        name  = Path(folder).name

        self.cover_data  = None
        self.cover_photo = None
        self._cover_gen  = getattr(self, '_cover_gen', 0) + 1
        self._local_cover_used = False
        self._covlbl.config(image="", text="okładka\nbrak")

        # Jeśli w folderze jest DOKŁADNIE JEDEN plik graficzny — to prawie na pewno
        # oryginalna okładka dołączona przez tego, kto przygotował audiobooka. Wklejamy
        # ją od razu, bez czekania na wyszukiwanie w internecie (i nie nadpisujemy jej
        # potem automatycznie wynikiem online — patrz _finish_search).
        local_cover_path = find_local_cover_image(folder)
        if local_cover_path:
            threading.Thread(target=self._local_cover_w,
                              args=(local_cover_path, self._cover_gen), daemon=True).start()

        self._fldr.config(text=name, fg=ACC2)
        self._flbl.config(
            text=f"{'✓' if total else '✗'}  {total} plików audio",
            fg=GREEN if total else RED)

        info = parse_folder(name)
        self.parsed_info = info

        self._ia.config(text=info.get("author", "") or "—")
        self._it.config(text=info.get("title", "")  or "—")
        self._in.config(text=info.get("narrator", "") or "—")
        self._iy.config(text={
            "audiobook": "📚 Audiobook", "music": "🎵 Muzyka"
        }.get(info.get("type", ""), "❓ Nieznany"))

        q = info.get("q_full", name)
        self._qv.set(q)

        for k in ("author", "title", "narrator"):
            if info.get(k) and k in self._ed:
                self._ed[k].set(info[k])

        self._ftree.delete(*self._ftree.get_children())
        for i, fp in enumerate(self.audio_files, 1):
            self._ftree.insert("", "end", iid=str(i),
                values=(f"{i:02d}", Path(fp).name, "Oczekuje"))

        self._log("", "dim")
        self._log(f"📁  {name}", "acc")
        self._log(f"    Autor:  {info.get('author', '?') or '(nie rozpoznano)'}", "ok")
        self._log(f"    Tytuł:  {info.get('title', '?')}", "ok")
        if info.get("narrator"):
            self._log(f"    Lektor: {info['narrator']}", "ok")
        self._log(f"    Pliki:  {total} szt.", "ok" if total else "err")
        self._log("── Szukam automatycznie… ──", "dim")

        self._stats_lbl.config(text="")
        if total > 0:
            threading.Thread(target=self._compute_stats_w, args=(list(self.audio_files),), daemon=True).start()

        try:
            add_to_history(folder)
            self._ui_call(self._refresh_history_ui)
        except Exception:
            pass

        if total > 0:
            self.after(500, self._search)

    def _compute_stats_w(self, files):
        try:
            stats = compute_library_stats(files)
            txt = f"⏱ {format_duration(stats['duration'])}   ·   💾 {format_size(stats['size'])}"
            self._ui_call(lambda: self._stats_lbl.config(text=txt))
        except Exception:
            pass

    def _refresh_history_ui(self):
        try:
            hist = load_history()
            self._hist_map = {Path(h).name or h: h for h in hist}
            self._hist_combo["values"] = list(self._hist_map.keys())
        except Exception:
            pass

    def _on_history_pick(self, _event=None):
        name = self._hist_var.get()
        folder = self._hist_map.get(name)
        if folder and os.path.isdir(folder):
            self._load(folder)
        elif folder:
            messagebox.showwarning("Brak folderu", f"Folder już nie istnieje:\n{folder}")

    def _search(self):
        # UWAGA: celowo NIE blokujemy tu na self._busy. Poprzednio blokada
        # "if self._busy: return" powodowała, że gdy użytkownik otwierał NOWY folder
        # zanim poprzednie (wolne) wyszukiwanie się skończyło, nowe wyszukiwanie
        # w ogóle się nie uruchamiało — a stary, wolny wątek i tak później dochodził
        # i nadpisywał już wyświetlony (poprawny) tytuł/okładkę danymi z POPRZEDNIEGO
        # folderu. To właśnie wyglądało jak "dane wypełniają się dobrze, a po chwili
        # zmienia się na inną książkę". Licznik generacji (_search_gen) poniżej
        # bezpiecznie odrzuca takie spóźnione wyniki, więc nowe wyszukiwanie może
        # zawsze wystartować od razu i po prostu wygrywa z poprzednim.
        q = self._qv.get().strip()
        if not q: return
        # licznik generacji wyszukiwania — pozwala odrzucić spóźnione wyniki wątków
        # z POPRZEDNIEGO wyszukiwania/folderu (to one powodowały "zmienianie się" książki
        # po chwili oraz losowe okładki: wolny wątek dogrywał się już do innego folderu)
        self._search_gen = getattr(self, '_search_gen', 0) + 1
        gen = self._search_gen
        self._user_picked = False
        self._auto_selecting = False
        self.search_results = []
        self.selected_idx = -1
        self._tree.delete(*self._tree.get_children())
        self._set_busy("Szukam metadanych…")
        self._prog(3)

        # Zawsze dodaj kandydata zbudowanego z samej nazwy folderu — gwarancja, że
        # poprawny tytuł/autor są zawsze widoczne na liście, nawet gdyby żadne
        # źródło internetowe go nie znalazło.
        pi = self.parsed_info
        if pi.get("title") or pi.get("author"):
            fallback = {
                "title": pi.get("title", ""), "author": pi.get("author", ""),
                "year": "", "genre": "Audiobook" if pi.get("type") == "audiobook" else "",
                "publisher": "", "cover_url": "", "source": "Nazwa folderu",
            }
            self._append_results([fallback], gen)

        threading.Thread(target=self._search_w, args=(q, gen), daemon=True).start()

    def _search_w(self, query, gen):
        pi = self.parsed_info
        variants = pi.get("query_variants") or [query]
        if query not in variants:
            variants = [query] + variants
        variants = variants[:3]  # ograniczenie liczby prób — dla szybkości

        sources = []
        if self._s_lc.get(): sources.append((search_lubimyczytac, "Lubimyczytac"))
        if self._s_at.get(): sources.append((search_audioteka, "Audioteka"))
        if self._s_em.get(): sources.append((search_empik, "Empik"))
        if self._s_gb.get(): sources.append((lambda q: search_google_books(q, True), "Google Books PL"))
        if self._s_ol.get(): sources.append((search_openlibrary, "Open Library"))
        if self._s_it.get(): sources.append((search_itunes, "iTunes"))
        if getattr(self, "_s_wiki", None) and self._s_wiki.get():
            sources.append((search_wikipedia_pl, "Wikipedia PL"))
        if getattr(self, "_s_nx", None) and self._s_nx.get():
            sources.append((search_nexto, "Nexto"))
        if getattr(self, "_s_tk", None) and self._s_tk.get():
            sources.append((search_taniaksiazka, "TaniaKsiazka"))

        if not sources:
            self._ui_call(lambda: self._finish_search(0, gen))
            return

        lock = threading.Lock()
        state = {"done": 0, "found": 0}
        total = len(sources)

        # Wszystkie źródła odpytywane RÓWNOLEGLE (każde we własnym wątku) —
        # jedno wolne/zablokowane źródło (np. Empik) nie blokuje już reszty.
        def run_one(fn, name):
            self._log(f"  → {name}…", "dim")
            r = []
            for v in variants:
                try:
                    r = fn(v)
                except Exception:
                    r = []
                if r:
                    break
            try:
                r.sort(key=lambda x: score_result(x, pi), reverse=True)
            except Exception:
                pass
            self._log(f"     {name}: {len(r)} wyników", "ok" if r else "err")
            with lock:
                state["done"] += 1
                state["found"] += len(r)
                done = state["done"]
            self._prog(int(done / total * 100))
            self._ui_call(lambda batch=r, gen=gen: self._append_results(batch, gen))
            if done >= total:
                self._ui_call(lambda n=state["found"], gen=gen: self._finish_search(n, gen))

        for fn, name in sources:
            threading.Thread(target=run_one, args=(fn, name), daemon=True).start()

    def _append_results(self, batch, gen=None):
        """Dokłada wyniki jednego źródła do tabeli bez czyszczenia (nie gubi wyboru użytkownika).
        Jeśli `gen` nie zgadza się z aktualnym numerem wyszukiwania — to spóźnione wyniki
        z poprzedniego folderu/zapytania i są ignorowane (naprawia "losowe" okładki/tytuły)."""
        if gen is not None and gen != getattr(self, "_search_gen", gen):
            return
        start = len(self.search_results)
        for i, r in enumerate(batch, start):
            self.search_results.append(r)
            self._tree.insert("", "end", iid=str(i), values=(
                r.get("title", ""),
                r.get("author", ""),
                r.get("year", ""),
                (r.get("genre", "") or "")[:30],
                (r.get("publisher", "") or "")[:25],
                r.get("source", ""),
            ))
    def _finish_search(self, total_found, gen=None):
        if gen is not None and gen != getattr(self, "_search_gen", gen):
            return  # spóźnione zakończenie poprzedniego wyszukiwania — ignoruj
        self._prog(0); self._set_busy("")
        self._log(f"  Łącznie: {total_found} wyników", "acc")
        if not self.search_results:
            self._log("  ⚠ Brak wyników — edytuj zapytanie i szukaj ponownie", "amb")
            return

        # Wybór najlepszego dopasowania NASTĘPUJE DOPIERO TERAZ, gdy wszystkie źródła
        # się już wypowiedziały — porównujemy WSZYSTKIE zebrane wyniki naraz i bierzemy
        # najwyżej oceniony (a nie ten, które źródło akurat odpowiedziało jako pierwsze —
        # to właśnie powodowało losowy/błędny wybór tytułu i okładki).
        if not getattr(self, "_user_picked", False):
            pi = self.parsed_info
            try:
                best_idx = max(range(len(self.search_results)),
                                key=lambda i: score_result(self.search_results[i], pi))
            except Exception:
                best_idx = 0
            self._auto_selecting = True
            try:
                self._tree.selection_set(str(best_idx))
                self._tree.see(str(best_idx))
                self._on_sel(None)
            finally:
                self._auto_selecting = False
            best = self.search_results[best_idx]
            self._log(f"  ✓ Wybrano najlepiej dopasowany wynik: „{best.get('title','')}” "
                      f"[{best.get('source','')}]", "ok")
            # Jeśli w folderze była dokładnie jedna okładka — już jej używamy i ufamy jej
            # bardziej niż czemukolwiek z internetu, więc NIE nadpisujemy jej automatycznie.
            if not getattr(self, "_local_cover_used", False):
                self.after(150, self._fetch_cover)

    def _on_sel(self, _):
        sel = self._tree.selection()
        if not sel: return
        idx = int(sel[0])
        if idx >= len(self.search_results): return
        # rozróżnij kliknięcie użytkownika od zaznaczenia ustawionego programowo
        # (przez auto-wybór najlepszego wyniku) — inaczej auto-wybór po zakończeniu
        # wyszukiwania nadpisywałby ręczny wybór, który użytkownik już zdążył zrobić
        if not getattr(self, "_auto_selecting", False):
            self._user_picked = True
        self.selected_idx = idx
        r = self.search_results[idx]
        self._stitle.config(text=r.get("title", "—"))
        display_author = self.parsed_info.get("author", "") or r.get("author", "")
        self._sauthor.config(text=display_author)
        parts = [x for x in [r.get("year", ""), r.get("genre", ""),
                              r.get("publisher", ""), f"[{r.get('source', '')}]"] if x]
        self._smeta.config(text="  •  ".join(parts))
        if r.get("title") and "title" in self._ed:
            self._ed["title"].set(r["title"])
        # rok/gatunek/wydawca zawsze z BIEŻĄCEGO wyniku — bez resztek z poprzedniego
        for k in ("year", "genre", "publisher"):
            if k in self._ed: self._ed[k].set(r.get(k, "") or "")
        # opis zawsze synchronizujemy z bieżącym wynikiem (nawet gdy pusty) — inaczej
        # przy przełączaniu między wynikami zostawałby stary, mylący opis poprzedniej książki
        if "description" in self._ed:
            self._ed["description"].set(r.get("description", ""))
        if self.parsed_info.get("author") and "author" in self._ed:
            self._ed["author"].set(self.parsed_info["author"])
        if self.parsed_info.get("narrator") and "narrator" in self._ed:
            self._ed["narrator"].set(self.parsed_info["narrator"])

    def _fetch_cover(self):
        if not (0 <= self.selected_idx < len(self.search_results)): return
        url = self.search_results[self.selected_idx].get("cover_url", "")
        if not url:
            self._log("  ⚠ Brak URL okładki dla tego wyniku", "amb"); return
        self._log("  🖼 Pobieranie okładki…", "dim")
        gen = getattr(self, '_cover_gen', 0)
        threading.Thread(target=self._cover_w, args=(url, gen), daemon=True).start()

    def _pick_cover_manually(self):
        """Pozwala ręcznie wskazać plik obrazu jako okładkę (np. zapisany z wyszukiwarki grafiki)."""
        path = filedialog.askopenfilename(
            title="Wybierz plik okładki",
            filetypes=[("Obrazy", "*.jpg *.jpeg *.png *.webp *.bmp *.gif"),
                       ("Wszystkie pliki", "*.*")])
        if not path:
            return
        jpeg_data = load_image_as_jpeg_cover(path)
        if not jpeg_data:
            messagebox.showerror("Błąd okładki", "Nie udało się wczytać tego obrazu.")
            return
        self._cover_gen = getattr(self, '_cover_gen', 0) + 1
        self._local_cover_used = True  # ręczny wybór też liczy się jako "pewna" okładka
        self.cover_data = jpeg_data
        self._log(f"  ✓ Okładka wczytana ręcznie ({len(jpeg_data)//1024} KB)", "ok")
        self._show_cover(jpeg_data, self._cover_gen)

    def _local_cover_w(self, path, gen):
        """Wczytuje jedyny plik graficzny znaleziony w folderze audiobooka jako okładkę —
        bez czekania na wyszukiwanie w internecie (patrz komentarz w _load)."""
        data = load_image_as_jpeg_cover(path)
        if gen != getattr(self, '_cover_gen', 0) or not data:
            return
        self.cover_data = data
        self._local_cover_used = True
        self._log(f"  🖼 Okładka z folderu: {Path(path).name} (użyto automatycznie)", "ok")
        self._ui_call(lambda: self._show_cover(data, gen))

    def _cover_w(self, url, gen):
        data = download_cover(url)
        if gen != getattr(self, '_cover_gen', 0):
            return
        if not data:
            self._log("  ✗ Nie pobrano okładki", "err")
            return
        try:
            img = Image.open(BytesIO(data))
            img.load()
            if img.mode not in ("RGB", "L"):
                img = img.convert("RGB")
            buf = BytesIO()
            img.save(buf, format="JPEG", quality=92)
            jpeg_data = buf.getvalue()
        except Exception as e:
            self._log(f"  ✗ Błąd obrazu: {e}", "err")
            return
        if gen != getattr(self, '_cover_gen', 0):
            return
        self.cover_data = jpeg_data
        self._log(f"  ✓ Okładka pobrana ({len(jpeg_data)//1024} KB)", "ok")
        self._ui_call(lambda: self._show_cover(jpeg_data, gen))

    def _show_cover(self, data, gen=None):
        if gen is not None and gen != getattr(self, '_cover_gen', 0):
            return
        try:
            ph = rounded_shadow_cover(data, box=162, radius=18)
            if ph is None:
                img = Image.open(BytesIO(data)).convert("RGB").resize((162, 162), Image.LANCZOS)
                ph = ImageTk.PhotoImage(img)
            self.cover_photo = ph
            self._covlbl.config(image=ph, text="", compound="center")
            self._covlbl.image = ph
            self._covlbl.update()
        except Exception as e:
            self._log(f"  ✗ Błąd podglądu: {e}", "err")

    def _final_tags(self) -> dict:
        tags = {}
        if 0 <= self.selected_idx < len(self.search_results):
            r = self.search_results[self.selected_idx]
            for k in ("title", "year", "genre", "publisher", "description"):
                if r.get(k): tags[k] = r[k]
            r_author = (r.get("author") or "").strip()
            r_title  = (r.get("title")  or "").strip()
            if r_author and r_author.lower() != r_title.lower():
                tags["author"] = r_author

        for k in ("author", "title", "narrator"):
            if self.parsed_info.get(k): tags[k] = self.parsed_info[k]
        for k, v in self._ed.items():
            val = v.get().strip()
            if val: tags[k] = val
        if not tags.get("genre") and self.parsed_info.get("type") == "audiobook":
            tags["genre"] = "Audiobook"
        if not tags.get("album"):
            tags["album"] = tags.get("title", "")
        return tags

    def _maybe_rename_files(self, files):
        """Numeruje pliki 01, 02… (jeśli włączone). Zwraca aktualną listę ścieżek."""
        if not (hasattr(self, "_s_rename") and self._s_rename.get()) or not files:
            return files
        try:
            plan = plan_renumber(files)
            if all(old == new for old, new in plan):
                return files
            new_files = apply_renumber(plan)
        except Exception as e:
            self._log(f"  ✗ Nie udało się ponumerować plików (zmiany cofnięto): {e}", "err")
            return files
        self._log("📑 Ponumerowano pliki:", "acc")
        self._ui_call(lambda: self._ftree.delete(*self._ftree.get_children()))
        for i, fp in enumerate(new_files, 1):
            self._log(f"   {i:02d}. {Path(fp).name}", "dim")
            self._ui_call(lambda iid=str(i), name=Path(fp).name:
                self._ftree.insert("", "end", iid=iid, values=(f"{iid.zfill(2)}", name, "Oczekuje")))
        return new_files

    def _apply(self):
        if self._writing:
            messagebox.showinfo("Trwa zapis", "Zapis tagów już trwa — poczekaj na zakończenie."); return
        if not self.audio_files:
            messagebox.showwarning("Brak plików", "Załaduj folder z plikami audio."); return
        tags = self._final_tags()
        self._log("", "dim")
        self._log("💾 Zapisuję tagi…", "acc")
        for k, label in [("title", "Tytuł"), ("author", "Autor"),
                          ("year", "Rok"), ("genre", "Gatunek"), ("narrator", "Lektor")]:
            if tags.get(k): self._log(f"   {label}: {tags[k]}", "ok")
        if self.cover_data: self._log("   Okładka: ✓", "ok")
        self._start_write(tags)

    def _start_write(self, tags):
        # "Zdjęcie" stanu w chwili kliknięcia Zapisz: folder, pliki i okładka.
        # Wcześniej wątek zapisu czytał self.cover_data / self.folder_path na bieżąco —
        # gdy w trakcie zapisu otwierało się następny audiobook, reszta plików dostawała
        # okładkę NASTĘPNEJ książki (albo żadnej), a cover.jpg lądował w złym folderze.
        job = {
            "folder": self.folder_path,
            "files":  list(self.audio_files),
            "cover":  self.cover_data,
            "book":   self.parsed_info.get("title") or "plikom",
            "gen":    self._load_gen,
        }
        self._writing = True
        self._set_busy("Zapisuję tagi…")
        threading.Thread(target=self._write_w, args=(tags, job), daemon=True).start()

    def _write_w(self, tags, job):
        ok = err = 0
        total = len(job["files"])
        try:
            files = self._maybe_rename_files(job["files"])
            if job["gen"] == self._load_gen:
                self.audio_files = files
            if job["cover"] and hasattr(self, "_s_savecover") and self._s_savecover.get():
                self._save_cover_silent(job["folder"], job["cover"])

            total = len(files)
            for i, path in enumerate(files, 1):
                self._prog(i / total * 100)
                name = Path(path).name
                success, reason = write_tags(path, tags, job["cover"], i, total)
                if success:
                    ok += 1
                    self._log(f"  ✓ {name}", "ok")
                    self._ui_call(lambda iid=str(i): self._ftree.set(iid, "status", "✓ OK")
                                  if self._ftree.exists(iid) else None)
                else:
                    err += 1
                    self._log(f"  ✗ {name}  ({reason})", "err")
                    self._ui_call(lambda iid=str(i): self._ftree.set(iid, "status", "✗ Błąd")
                                  if self._ftree.exists(iid) else None)
        except Exception as e:
            err += 1
            _flog.error("Błąd zapisu tagów w %s", job["folder"], exc_info=True)
            self._log(f"  ✗ Błąd zapisu: {e}", "err")
        finally:
            self._writing = False
            self._ui_call(lambda: self._set_busy(""))
            self._ui_call(lambda: self.after(1500, lambda: self._pv.set(0)))
        self._log("", "dim")
        self._log(f"{'✅' if err == 0 else '⚠'}  Gotowe!  OK: {ok}  Błędy: {err}",
                  "ok" if err == 0 else "amb")
        if err == 0:
            self._toast(f"✅  Zapisano tagi ({ok}/{total}) — „{job['book']}” gotowe do Plex!", "ok")
        else:
            self._toast(f"⚠  Zapisano {ok}/{total} plików, {err} z błędem — szczegóły w panelu "
                        f"DZIENNIK (po lewej) i w pliku audiotagai_dziennik.log", "amb", ms=9000)

    def _apply_manual(self):
        if self._writing:
            messagebox.showinfo("Trwa zapis", "Zapis tagów już trwa — poczekaj na zakończenie."); return
        tags = {k: v.get().strip() for k, v in self._ed.items() if v.get().strip()}
        if not tags:
            messagebox.showwarning("Puste pola", "Wypełnij przynajmniej jedno pole."); return
        if not self.audio_files:
            messagebox.showwarning("Brak plików", "Załaduj folder z plikami audio."); return
        if not tags.get("album"): tags["album"] = tags.get("title", "")
        self._log("💾 Zapisuję ręczne tagi…", "acc")
        self._start_write(tags)

    # ── Pomocniki ─────────────────────────────────────────────────────────

    def _log(self, msg, tag="dim"):
        try:
            text = msg.strip()
            if text and not text[0] in "╔║╚":
                lvl = {"err": logging.ERROR, "amb": logging.WARNING}.get(tag, logging.INFO)
                _flog.log(lvl, text)
        except Exception:
            pass
        self.log_q.put((msg, tag))

    def _ui_call(self, fn):
        """Bezpieczne zlecenie zmiany w oknie z wątku roboczego (Tkinter nie jest
        wielowątkowy — wołanie go bezpośrednio z wątków powodowało losowe błędy)."""
        self._ui_q.put(fn)

    _LOG_MAX_LINES = 3000

    def _flush_log(self):
        # 1) zlecenia GUI z wątków
        for _ in range(500):
            try:
                fn = self._ui_q.get_nowait()
            except queue.Empty:
                break
            try:
                fn()
            except Exception:
                _flog.error("Błąd aktualizacji okna", exc_info=True)
        # 2) wpisy do panelu DZIENNIK
        wrote = False
        try:
            while True:
                msg, tag = self.log_q.get_nowait()
                if not wrote:
                    self._log_box.configure(state="normal"); wrote = True
                self._log_box.insert("end", msg + "\n", tag)
        except queue.Empty:
            pass
        if wrote:
            # ograniczamy panel, żeby przy dużych partiach okno nie zwalniało
            lines = int(self._log_box.index("end-1c").split(".")[0])
            if lines > self._LOG_MAX_LINES:
                self._log_box.delete("1.0", f"{lines - self._LOG_MAX_LINES}.0")
            self._log_box.see("end")
            self._log_box.configure(state="disabled")
        self.after(80, self._flush_log)

    def _open_log_file(self):
        if LOG_FILE and LOG_FILE.exists():
            try:
                os.startfile(str(LOG_FILE))   # Windows: otwiera w Notatniku
                return
            except Exception:
                pass
            messagebox.showinfo("Plik dziennika", f"Plik dziennika:\n{LOG_FILE}")
        else:
            messagebox.showwarning("Plik dziennika", "Plik dziennika nie został jeszcze utworzony.")

    def _save_cover_silent(self, folder=None, data=None):
        """Zapisuje okładkę do folderu bez okien dialogowych (używane automatycznie przy zapisie tagów)."""
        folder = folder or self.folder_path
        data = data or self.cover_data
        if not data or not folder:
            return
        try:
            cover_path = os.path.join(folder, "cover.jpg")
            with open(cover_path, "wb") as f:
                f.write(data)
            self._log("  ✓ Okładka zapisana jako cover.jpg", "ok")
        except Exception as e:
            self._log(f"  ✗ Błąd zapisu okładki: {e}", "err")

    def _save_cover_to_folder(self):
        """Zapisuje aktualnie pobraną okładkę jako JPG w wybranym folderze audio (ręcznie, z przyciskiem)."""
        if not self.cover_data:
            self._log("  ⚠ Najpierw pobierz okładkę", "amb")
            messagebox.showwarning("Brak okładki", "Najpierw kliknij: Pobierz okładkę.")
            return

        if not self.folder_path:
            self._log("  ⚠ Brak folderu docelowego", "err")
            messagebox.showwarning("Brak folderu", "Najpierw wybierz folder z plikami audio.")
            return

        try:
            title = self.parsed_info.get("title", "okladka") or "okladka"
            safe_title = re.sub(r'[\\/*?:"<>|]', "_", title).strip() or "okladka"

            cover_path = os.path.join(self.folder_path, "cover.jpg")
            named_path = os.path.join(self.folder_path, f"{safe_title}.jpg")

            with open(cover_path, "wb") as f:
                f.write(self.cover_data)

            if os.path.abspath(named_path) != os.path.abspath(cover_path):
                with open(named_path, "wb") as f:
                    f.write(self.cover_data)

            self._log("  ✓ Okładka zapisana do folderu: cover.jpg", "ok")
            if os.path.basename(named_path) != "cover.jpg":
                self._log(f"  ✓ Kopia zapisana jako: {os.path.basename(named_path)}", "ok")

        except Exception as e:
            self._log(f"  ✗ Błąd zapisu okładki: {e}", "err")
            messagebox.showerror("Błąd zapisu", f"Nie udało się zapisać okładki:\n{e}")

    def _prog(self, v): self._ui_call(lambda: self._pv.set(v))
    def _set_busy(self, m): self._busy = bool(m); self._busy_lbl.config(text=m)

    def _toast(self, msg: str, kind: str = "ok", ms: int = 4200):
        """Krótki, kolorowy pasek powiadomienia u góry okna (np. 'Zapisano tagi do 42 plików!')."""
        def show():
            colors = {"ok": ("#0b3d2e", GREEN), "err": ("#3d0b0b", RED), "amb": ("#3d310b", AMBER)}
            bgc, fgc = colors.get(kind, colors["ok"])
            self._toast_lbl.config(text=msg, bg=bgc, fg=fgc)
            self._toast_lbl.pack(fill="x", before=self._content_frame)
            self._toast_gen = getattr(self, "_toast_gen", 0) + 1
            gen = self._toast_gen
            self.after(ms, lambda: self._hide_toast(gen))
        self._ui_call(show)

    def _hide_toast(self, gen):
        if gen == getattr(self, "_toast_gen", 0):
            self._toast_lbl.pack_forget()


# ─── Małe pomocniki ───────────────────────────────────────────────────────

def _sep(p):
    tk.Frame(p, bg=BORDER, height=1).pack(fill="x", padx=14, pady=5)

def _lbl(p, text):
    tk.Label(p, text=text, bg=BG, fg=MUTED,
             font=("Segoe UI", 8, "bold")).pack(anchor="w", padx=14, pady=(8, 3))

def _irow(card, label):
    r = tk.Frame(card, bg=CARD); r.pack(fill="x", padx=10, pady=2)
    tk.Label(r, text=label, bg=CARD, fg=MUTED,
             font=("Segoe UI", 8), width=9, anchor="w").pack(side="left")
    v = tk.Label(r, text="—", bg=CARD, fg=TEXT,
                 font=("Segoe UI", 9, "bold"), anchor="w", wraplength=220)
    v.pack(side="left", fill="x", expand=True)
    return v

def _pill(p, text, color, bg=PANEL):
    """Mała, zaokrąglona 'plakietka' (badge) — np. PREMIUM przy tytule."""
    c = tk.Canvas(p, height=17, bg=bg, highlightthickness=0)
    w = 12 + len(text) * 6
    c.configure(width=w)
    c.create_rectangle(0, 0, w, 17, fill=bg, width=0)
    r = 8
    c.create_oval(0, 0, r * 2, 17, fill=color, outline="")
    c.create_oval(w - r * 2, 0, w, 17, fill=color, outline="")
    c.create_rectangle(r, 0, w - r, 17, fill=color, width=0)
    c.create_text(w / 2, 9, text=text, fill=PANEL, font=("Segoe UI", 7, "bold"))
    c.pack(side="left", padx=(8, 0), pady=(2, 0))
    return c


# ═══════════════════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════════════════

if __name__ == "__main__":
    setup_file_log()
    App().mainloop()
