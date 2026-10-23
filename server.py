termux_server.py


#!/usr/bin/env python3
"""
termux_server.py — Lightweight, zero-dependency HTTP file server for Termux.
Features:
  - Termux-inspired dark minimalist UI with monospace typography
  - Sticky breadcrumb navigation bar at the top
  - Hamburger menu: Select mode, + Upload Files, + New Folder, + New Text File, Show .dotfiles (OFF by default)
  - Hidden-by-default checkboxes; Select mode reveals checkboxes & action bar (Copy, Move, Rename, Edit, Zip, Extract, Delete)
  - Persistent cross-folder clipboard bar (Copy/Cut items, navigate via breadcrumbs, Paste Here)
  - Top monochrome upload progress bar + drag-and-drop uploads + streamed multipart disk writes
  - Bottom storage usage bar showing free space / total space and color-coded fill meter
  - Inline Text Viewer & Editor modal (with Open in browser button, live cursor Ln/Col indicator, Tab support, Ctrl+S, and auto-open on New Text File)
  - Image & Media Lightbox modal with Prev / Open / Next buttons, Download icon, Fullscreen mode, and Left/Right edge tap zones
  - Optional HTTP Basic Authentication (-a / --auth user:pass)

Usage in Termux:
  python termux_server.py [port] [-d DIRECTORY] [-a USER:PASS]
"""

import argparse
import base64
import datetime
import hmac
import html
import io
import json
import os
import posixpath
import re
import shutil
import socket
import sys
import tarfile
import tempfile
import urllib.parse
import zipfile
from http import HTTPStatus
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer

SERVER_ROOT = os.getcwd()
SERVER_AUTH_TOKEN = None  # Base64 "user:pass" when --auth is enabled

TEXT_EXTENSIONS = {
    ".txt", ".md", ".log", ".rst", ".csv", ".tsv", ".py", ".sh", ".bash", ".zsh",
    ".js", ".mjs", ".ts", ".tsx", ".jsx", ".json", ".html", ".htm", ".css", ".scss",
    ".c", ".h", ".cpp", ".hpp", ".rs", ".go", ".java", ".kt", ".kts", ".xml",
    ".yaml", ".yml", ".toml", ".ini", ".conf", ".cfg", ".sql", ".lua", ".rb",
    ".php", ".vim", ".env", ".gitignore", ".bashrc", ".zshrc", ".properties",
}

EXTRACTABLE_SUFFIXES = (
    ".zip", ".tar", ".tar.gz", ".tgz", ".tar.bz2", ".tbz2", ".tar.xz", ".txz",
)

FILE_CATEGORIES = {
    "code": {
        "exts": {
            ".py", ".sh", ".bash", ".zsh", ".js", ".mjs", ".ts", ".tsx", ".jsx",
            ".json", ".html", ".htm", ".css", ".scss", ".c", ".h", ".cpp", ".hpp",
            ".rs", ".go", ".java", ".kt", ".kts", ".xml", ".yaml", ".yml", ".toml",
            ".ini", ".conf", ".cfg", ".sql", ".lua", ".rb", ".php", ".vim",
        },
        "badge": "CODE",
        "class": "ft-code",
    },
    "media": {
        "exts": {
            ".mp4", ".mkv", ".webm", ".avi", ".mov", ".flv", ".m4v",
            ".mp3", ".flac", ".wav", ".ogg", ".m4a", ".aac", ".opus",
        },
        "badge": "MEDIA",
        "class": "ft-media",
    },
    "image": {
        "exts": {
            ".jpg", ".jpeg", ".png", ".gif", ".webp", ".svg", ".bmp", ".ico", ".avif", ".heic",
        },
        "badge": "IMG",
        "class": "ft-img",
    },
    "archive": {
        "exts": {
            ".zip", ".tar", ".gz", ".tgz", ".bz2", ".tbz2", ".xz", ".txz", ".zst",
            ".7z", ".rar", ".apk", ".deb", ".iso", ".img",
        },
        "badge": "PKG",
        "class": "ft-pkg",
    },
    "doc": {
        "exts": {
            ".pdf", ".md", ".txt", ".log", ".rst", ".csv", ".tsv",
            ".doc", ".docx", ".xls", ".xlsx", ".ppt", ".pptx", ".epub", ".mobi",
        },
        "badge": "DOC",
        "class": "ft-doc",
    },
}


def classify_file(name: str, is_dir: bool, is_link: bool):
    if is_dir:
        return ("DIR", "ft-dir")
    if is_link:
        return ("LINK", "ft-link")
    _, ext = os.path.splitext(name.lower())
    for cat in FILE_CATEGORIES.values():
        if ext in cat["exts"]:
            return (cat["badge"], cat["class"])
    return ("FILE", "ft-file")


def is_text_editable(name: str, is_dir: bool) -> bool:
    if is_dir:
        return False
    lower = name.lower()
    if lower in TEXT_EXTENSIONS:
        return True
    _, ext = os.path.splitext(lower)
    return ext in TEXT_EXTENSIONS


def is_extractable_archive(name: str, is_dir: bool) -> bool:
    if is_dir:
        return False
    lower = name.lower()
    return any(lower.endswith(sfx) for sfx in EXTRACTABLE_SUFFIXES)


def strip_archive_suffix(name: str) -> str:
    lower = name.lower()
    for sfx in sorted(EXTRACTABLE_SUFFIXES, key=len, reverse=True):
        if lower.endswith(sfx):
            return name[: len(name) - len(sfx)] or "extracted"
    return os.path.splitext(name)[0] or "extracted"


def human_size(num_bytes: int) -> str:
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if num_bytes < 1024 or unit == "TB":
            return f"{num_bytes:.0f} B" if unit == "B" else f"{num_bytes:.1f} {unit}"
        num_bytes /= 1024.0
    return f"{num_bytes:.1f} TB"


def resolve_safe_path(rel_url_path: str) -> str:
    """Resolve a URL-style relative path safely inside SERVER_ROOT."""
    cleaned = urllib.parse.unquote(rel_url_path or "/").lstrip("/")
    norm_rel = os.path.normpath(cleaned) if cleaned else "."
    target = os.path.abspath(os.path.join(SERVER_ROOT, norm_rel))
    if os.path.commonpath([SERVER_ROOT, target]) != SERVER_ROOT:
        raise ValueError("Path escapes root directory")
    return target


def unique_dest_path(dest_dir: str, basename: str) -> str:
    """Return a non-colliding path inside dest_dir, appending ' (copy N)' if needed."""
    candidate = os.path.join(dest_dir, basename)
    if not os.path.exists(candidate) and not os.path.islink(candidate):
        return candidate
    stem, ext = os.path.splitext(basename)
    counter = 1
    while True:
        new_name = f"{stem} (copy {counter}){ext}" if counter > 1 else f"{stem} (copy){ext}"
        candidate = os.path.join(dest_dir, new_name)
        if not os.path.exists(candidate) and not os.path.islink(candidate):
            return candidate
        counter += 1


def safe_extract_archive(archive_path: str, extract_dir: str):
    """Safely extract zip or tar archives while preventing path traversal."""
    lower = archive_path.lower()
    abs_dest = os.path.abspath(extract_dir)
    if lower.endswith(".zip"):
        with zipfile.ZipFile(archive_path, "r") as zf:
            for member in zf.infolist():
                target = os.path.abspath(os.path.join(abs_dest, member.filename))
                if os.path.commonpath([abs_dest, target]) != abs_dest:
                    raise ValueError(f"Unsafe path in zip archive: {member.filename}")
            zf.extractall(abs_dest)
    else:
        with tarfile.open(archive_path, "r:*") as tf:
            for member in tf.getmembers():
                target = os.path.abspath(os.path.join(abs_dest, member.name))
                if os.path.commonpath([abs_dest, target]) != abs_dest:
                    raise ValueError(f"Unsafe path in tar archive: {member.name}")
            tf.extractall(abs_dest)


class TermuxHTTPRequestHandler(SimpleHTTPRequestHandler):
    server_version = "TermuxHTTP/3.1"

    def end_headers(self):
        self.send_header("Accept-Ranges", "bytes")
        super().end_headers()

    def check_auth(self) -> bool:
        if not SERVER_AUTH_TOKEN:
            return True
        auth_header = self.headers.get("Authorization", "")
        if auth_header.startswith("Basic "):
            provided = auth_header[6:].strip()
            if hmac.compare_digest(provided, SERVER_AUTH_TOKEN):
                return True
        self.send_response(HTTPStatus.UNAUTHORIZED)
        self.send_header("WWW-Authenticate", 'Basic realm="Termux HTTP Server"')
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        msg = b"401 Unauthorized\n"
        self.send_header("Content-Length", str(len(msg)))
        self.end_headers()
        self.wfile.write(msg)
        return False

    def send_json(self, status: int, payload: dict):
        data = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_HEAD(self):
        if not self.check_auth():
            return
        super().do_HEAD()

    def do_GET(self):
        if not self.check_auth():
            return
        parsed = urllib.parse.urlsplit(self.path)
        if parsed.query:
            qs = urllib.parse.parse_qs(parsed.query)
            if qs.get("action") == ["zip"]:
                items = qs.get("item", [])
                self.handle_zip_download(items)
                return

        range_header = self.headers.get("Range")
        if range_header:
            path = self.translate_path(self.path)
            if os.path.isfile(path):
                self.send_range_response(path, range_header)
                return
        super().do_GET()

    def do_POST(self):
        if not self.check_auth():
            return
        content_type = self.headers.get("Content-Type", "")
        if "application/json" in content_type:
            self.handle_api_action()
            return
        if "multipart/form-data" in content_type:
            self.handle_file_upload(content_type)
            return
        self.send_error(HTTPStatus.BAD_REQUEST, "Unsupported Content-Type")

    def handle_zip_download(self, items: list):
        """Package selected files/directories into a streamed temporary .zip archive."""
        try:
            if not items:
                self.send_error(HTTPStatus.BAD_REQUEST, "No items selected for zip")
                return
            resolved = []
            for rel in items:
                target = resolve_safe_path(rel)
                if os.path.exists(target):
                    resolved.append((rel, target))
            if not resolved:
                self.send_error(HTTPStatus.NOT_FOUND, "Selected items not found")
                return

            if len(resolved) == 1:
                base_label = os.path.basename(resolved[0][1].rstrip("/\\")) or "archive"
                zip_name = f"{base_label}.zip"
            else:
                zip_name = "selected_files.zip"

            with tempfile.SpooledTemporaryFile(max_size=16 * 1024 * 1024) as tmp_zip:
                with zipfile.ZipFile(tmp_zip, mode="w", compression=zipfile.ZIP_DEFLATED) as zf:
                    for _, full_path in resolved:
                        base_name = os.path.basename(full_path.rstrip("/\\"))
                        if os.path.isdir(full_path) and not os.path.islink(full_path):
                            parent_dir = os.path.dirname(full_path.rstrip("/\\"))
                            for root, dirs, files in os.walk(full_path):
                                rel_root = os.path.relpath(root, parent_dir)
                                if not files and not dirs:
                                    zf.writestr(rel_root.rstrip("/") + "/", "")
                                for fname in files:
                                    fpath = os.path.join(root, fname)
                                    if os.path.isfile(fpath):
                                        arcname = os.path.join(rel_root, fname)
                                        zf.write(fpath, arcname)
                        elif os.path.isfile(full_path):
                            zf.write(full_path, base_name)

                size = tmp_zip.tell()
                tmp_zip.seek(0)
                self.send_response(HTTPStatus.OK)
                self.send_header("Content-Type", "application/zip")
                safe_zip_name = urllib.parse.quote(zip_name)
                self.send_header(
                    "Content-Disposition",
                    f"attachment; filename=\"{zip_name}\"; filename*=UTF-8''{safe_zip_name}",
                )
                self.send_header("Content-Length", str(size))
                self.end_headers()
                shutil.copyfileobj(tmp_zip, self.wfile, length=64 * 1024)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as exc:
            self.send_error(HTTPStatus.BAD_REQUEST, str(exc))

    def handle_file_upload(self, content_type: str):
        """Stream multipart/form-data file uploads directly to disk without RAM spikes."""
        path = self.translate_path(self.path)
        if not os.path.isdir(path):
            self.send_error(HTTPStatus.BAD_REQUEST, "Target path is not a directory")
            return

        boundary_match = re.search(r"boundary=([^;\s]+)", content_type)
        if not boundary_match:
            self.send_error(HTTPStatus.BAD_REQUEST, "Missing multipart boundary")
            return

        boundary_bytes = boundary_match.group(1).strip('"').encode("utf-8")
        delim = b"--" + boundary_bytes
        remaining = int(self.headers.get("Content-Length", 0))

        def read_line() -> bytes:
            nonlocal remaining
            if remaining <= 0:
                return b""
            line = self.rfile.readline(min(remaining, 65536))
            remaining -= len(line)
            return line

        # Advance to first boundary
        while remaining > 0:
            line = read_line()
            if not line:
                break
            if line.strip().startswith(delim):
                break

        while remaining > 0:
            # Parse part headers
            headers_raw = []
            while remaining > 0:
                line = read_line()
                if not line or line in (b"\r\n", b"\n"):
                    break
                headers_raw.append(line.decode("utf-8", errors="replace"))

            if not headers_raw:
                break

            header_block = "".join(headers_raw)
            fn_match = re.search(r'filename="([^"]*)"', header_block)
            filename = os.path.basename(fn_match.group(1)) if (fn_match and fn_match.group(1)) else None

            out_file = None
            if filename:
                dest_path = os.path.join(path, filename)
                out_file = open(dest_path, "wb")

            # Stream part body until next boundary line, holding trailing \r\n in prev_tail
            prev_tail = b""
            try:
                while remaining > 0:
                    line = read_line()
                    if not line:
                        break
                    stripped = line.rstrip(b"\r\n")
                    if stripped == delim or stripped == delim + b"--":
                        # Trim the CRLF that preceded the boundary
                        if prev_tail.endswith(b"\r\n"):
                            prev_tail = prev_tail[:-2]
                        elif prev_tail.endswith(b"\n"):
                            prev_tail = prev_tail[:-1]
                        if out_file and prev_tail:
                            out_file.write(prev_tail)
                        prev_tail = b""
                        break
                    if out_file and prev_tail:
                        out_file.write(prev_tail)
                    prev_tail = line
            finally:
                if out_file:
                    out_file.close()

        self.send_response(HTTPStatus.SEE_OTHER)
        self.send_header("Location", self.path)
        self.end_headers()

    def handle_api_action(self):
        """Handle JSON file operations: delete, rename, copy, move, mkdir, touch, read_text, write_text, extract."""
        try:
            content_length = int(self.headers.get("Content-Length", 0))
            raw = self.rfile.read(content_length).decode("utf-8")
            data = json.loads(raw) if raw else {}
        except Exception as exc:
            self.send_json(HTTPStatus.BAD_REQUEST, {"ok": False, "error": f"Invalid JSON: {exc}"})
            return

        action = data.get("action")
        try:
            if action == "delete":
                items = data.get("items", [])
                if not items:
                    raise ValueError("No items specified for deletion")
                deleted = 0
                for rel in items:
                    target = resolve_safe_path(rel)
                    if target == SERVER_ROOT:
                        raise ValueError("Cannot delete server root directory")
                    if os.path.islink(target) or os.path.isfile(target):
                        os.unlink(target)
                        deleted += 1
                    elif os.path.isdir(target):
                        shutil.rmtree(target)
                        deleted += 1
                self.send_json(HTTPStatus.OK, {"ok": True, "deleted": deleted})

            elif action == "rename":
                src_rel = data.get("src", "")
                new_name = (data.get("new_name") or "").strip()
                if not src_rel or not new_name:
                    raise ValueError("Source and new name are required")
                if "/" in new_name or "\\" in new_name or new_name in (".", ".."):
                    raise ValueError("Invalid file or folder name")
                src_path = resolve_safe_path(src_rel)
                if src_path == SERVER_ROOT:
                    raise ValueError("Cannot rename server root")
                dest_path = os.path.join(os.path.dirname(src_path), new_name)
                if os.path.exists(dest_path) or os.path.islink(dest_path):
                    raise ValueError(f"'{new_name}' already exists")
                os.rename(src_path, dest_path)
                self.send_json(HTTPStatus.OK, {"ok": True})

            elif action in ("copy", "move"):
                items = data.get("items", [])
                dest_rel = data.get("dest_dir", "/")
                if not items:
                    raise ValueError("No items selected")
                dest_dir = resolve_safe_path(dest_rel)
                if not os.path.isdir(dest_dir):
                    raise ValueError("Destination directory does not exist")

                processed = 0
                for rel in items:
                    src_path = resolve_safe_path(rel)
                    if src_path == SERVER_ROOT:
                        raise ValueError("Cannot copy or move root directory")
                    if not os.path.exists(src_path) and not os.path.islink(src_path):
                        continue
                    basename = os.path.basename(src_path.rstrip("/\\"))
                    if action == "copy":
                        target_path = unique_dest_path(dest_dir, basename)
                        if os.path.isdir(src_path) and not os.path.islink(src_path):
                            if os.path.commonpath([src_path, target_path]) == src_path:
                                raise ValueError(f"Cannot copy folder '{basename}' into itself")
                            shutil.copytree(src_path, target_path, symlinks=True)
                        else:
                            shutil.copy2(src_path, target_path, follow_symlinks=False)
                        processed += 1
                    else:  # move
                        target_path = os.path.join(dest_dir, basename)
                        if os.path.abspath(src_path) == os.path.abspath(target_path):
                            continue
                        if os.path.exists(target_path) or os.path.islink(target_path):
                            raise ValueError(f"'{basename}' already exists in destination")
                        if os.path.isdir(src_path) and os.path.commonpath([src_path, dest_dir]) == src_path:
                            raise ValueError(f"Cannot move folder '{basename}' into itself")
                        shutil.move(src_path, target_path)
                        processed += 1

                self.send_json(HTTPStatus.OK, {"ok": True, "processed": processed})

            elif action == "mkdir":
                dir_rel = data.get("dir", "/")
                folder_name = (data.get("name") or "").strip()
                if not folder_name or "/" in folder_name or "\\" in folder_name or folder_name in (".", ".."):
                    raise ValueError("Invalid folder name")
                parent_dir = resolve_safe_path(dir_rel)
                new_dir = os.path.join(parent_dir, folder_name)
                if os.path.exists(new_dir):
                    raise ValueError(f"'{folder_name}' already exists")
                os.makedirs(new_dir)
                self.send_json(HTTPStatus.OK, {"ok": True})

            elif action == "touch":
                dir_rel = data.get("dir", "/")
                file_name = (data.get("name") or "").strip()
                if not file_name or "/" in file_name or "\\" in file_name or file_name in (".", ".."):
                    raise ValueError("Invalid file name")
                if "." not in file_name:
                    file_name += ".txt"
                parent_dir = resolve_safe_path(dir_rel)
                new_file = os.path.join(parent_dir, file_name)
                if os.path.exists(new_file) or os.path.islink(new_file):
                    raise ValueError(f"'{file_name}' already exists")
                with open(new_file, "w", encoding="utf-8") as f:
                    f.write("")
                rel_created = posixpath.join(dir_rel, file_name)
                self.send_json(HTTPStatus.OK, {"ok": True, "path": rel_created, "name": file_name})

            elif action == "read_text":
                rel_path = data.get("path", "")
                target = resolve_safe_path(rel_path)
                if not os.path.isfile(target):
                    raise ValueError("File does not exist")
                size = os.path.getsize(target)
                if size > 2 * 1024 * 1024:
                    raise ValueError("File is larger than 2 MB; download to edit locally")
                with open(target, "r", encoding="utf-8", errors="replace") as f:
                    content = f.read()
                self.send_json(
                    HTTPStatus.OK,
                    {"ok": True, "path": rel_path, "name": os.path.basename(target), "content": content},
                )

            elif action == "write_text":
                rel_path = data.get("path", "")
                content = data.get("content", "")
                target = resolve_safe_path(rel_path)
                if os.path.isdir(target):
                    raise ValueError("Cannot overwrite a directory with text")
                with open(target, "w", encoding="utf-8") as f:
                    f.write(content)
                self.send_json(HTTPStatus.OK, {"ok": True})

            elif action == "extract":
                src_rel = data.get("src", "")
                src_path = resolve_safe_path(src_rel)
                if not os.path.isfile(src_path):
                    raise ValueError("Archive file not found")
                parent_dir = os.path.dirname(src_path)
                folder_stem = strip_archive_suffix(os.path.basename(src_path))
                extract_dir = unique_dest_path(parent_dir, folder_stem)
                os.makedirs(extract_dir, exist_ok=True)
                try:
                    safe_extract_archive(src_path, extract_dir)
                except Exception:
                    shutil.rmtree(extract_dir, ignore_errors=True)
                    raise
                self.send_json(
                    HTTPStatus.OK,
                    {"ok": True, "extracted_to": os.path.basename(extract_dir)},
                )

            else:
                self.send_json(HTTPStatus.BAD_REQUEST, {"ok": False, "error": f"Unknown action: {action}"})
        except Exception as exc:
            self.send_json(HTTPStatus.BAD_REQUEST, {"ok": False, "error": str(exc)})

    def send_range_response(self, path: str, range_header: str):
        try:
            file_size = os.path.getsize(path)
            m = re.match(r"bytes=(\d*)-(\d*)", range_header)
            if not m:
                self.send_error(HTTPStatus.REQUESTED_RANGE_NOT_SATISFIABLE)
                return

            start_str, end_str = m.groups()
            start = int(start_str) if start_str else 0
            end = int(end_str) if end_str else file_size - 1
            if start >= file_size or start > end:
                self.send_response(HTTPStatus.REQUESTED_RANGE_NOT_SATISFIABLE)
                self.send_header("Content-Range", f"bytes */{file_size}")
                self.end_headers()
                return

            end = min(end, file_size - 1)
            length = end - start + 1
            ctype = self.guess_type(path)

            with open(path, "rb") as f:
                f.seek(start)
                self.send_response(HTTPStatus.PARTIAL_CONTENT)
                self.send_header("Content-Type", ctype)
                self.send_header("Content-Range", f"bytes {start}-{end}/{file_size}")
                self.send_header("Content-Length", str(length))
                self.send_header("Last-Modified", self.date_time_string(os.path.getmtime(path)))
                self.end_headers()
                remaining = length
                buf_size = 64 * 1024
                while remaining > 0:
                    chunk = f.read(min(buf_size, remaining))
                    if not chunk:
                        break
                    self.wfile.write(chunk)
                    remaining -= len(chunk)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def list_directory(self, path: str):
        try:
            entries = os.listdir(path)
        except OSError:
            self.send_error(HTTPStatus.NOT_FOUND, "No permission to list directory")
            return None

        url_path = urllib.parse.unquote(self.path.split("?", 1)[0])
        if not url_path.startswith("/"):
            url_path = "/" + url_path
        if not url_path.endswith("/"):
            url_path += "/"

        # Build breadcrumb segments
        segments = [seg for seg in url_path.strip("/").split("/") if seg]
        crumbs_html = ['<a href="/" class="crumb root-crumb">~</a>']
        accum = ""
        for idx, seg in enumerate(segments):
            accum += "/" + urllib.parse.quote(seg)
            is_last = idx == len(segments) - 1
            cls = "crumb active-crumb" if is_last else "crumb"
            crumbs_html.append('<span class="crumb-sep">/</span>')
            crumbs_html.append(f'<a href="{accum}/" class="{cls}">{html.escape(seg)}</a>')
        breadcrumb_bar = "".join(crumbs_html)

        items = []
        dir_count = 0
        file_count = 0
        for name in entries:
            full_path = os.path.join(path, name)
            is_dir = os.path.isdir(full_path)
            is_link = os.path.islink(full_path)
            try:
                st = os.stat(full_path)
                size = st.st_size if not is_dir else -1
                mtime = st.st_mtime
            except OSError:
                size = 0
                mtime = 0

            if is_dir:
                dir_count += 1
            else:
                file_count += 1

            badge, css_class = classify_file(name, is_dir, is_link)
            editable = 1 if is_text_editable(name, is_dir) else 0
            extractable = 1 if is_extractable_archive(name, is_dir) else 0
            preview_kind = ""
            if css_class == "ft-img":
                preview_kind = "image"
            elif css_class == "ft-media":
                ext = os.path.splitext(name.lower())[1]
                preview_kind = "audio" if ext in {".mp3", ".flac", ".wav", ".ogg", ".m4a", ".aac", ".opus"} else "video"

            display_name = name + "/" if is_dir else name
            href = urllib.parse.quote(name, errors="surrogatepass") + ("/" if is_dir else "")
            rel_item_path = posixpath.join(url_path, name)
            size_str = "—" if is_dir else human_size(size)
            mtime_str = (
                datetime.datetime.fromtimestamp(mtime).strftime("%Y-%m-%d %H:%M")
                if mtime
                else "—"
            )
            items.append({
                "name": name,
                "display_name": display_name,
                "href": href,
                "rel_path": rel_item_path,
                "is_dir": 1 if is_dir else 0,
                "editable": editable,
                "extractable": extractable,
                "preview": preview_kind,
                "size": size,
                "size_str": size_str,
                "mtime": mtime,
                "mtime_str": mtime_str,
                "badge": badge,
                "css_class": css_class,
                "hidden": name.startswith("."),
            })

        # Sort directories first, then alphabetically case-insensitive
        items.sort(key=lambda x: (-x["is_dir"], x["name"].lower()))

        rows_html = []
        if url_path != "/":
            parent_href = posixpath.normpath(url_path.rstrip("/") + "/..")
            if not parent_href.endswith("/"):
                parent_href += "/"
            rows_html.append(
                f'<tr class="parent-row" data-isdir="2" data-name=".." data-size="-1" data-mtime="0">'
                f'<td class="col-check"></td>'
                f'<td class="col-name"><a href="{parent_href}" class="row-link ft-dir">'
                f'<span class="badge badge-dir">UP</span><span class="fname">.. (Parent Directory)</span></a></td>'
                f'<td class="col-size">—</td>'
                f'<td class="col-date">—</td>'
                f"</tr>"
            )

        for it in items:
            hidden_attr = ' data-hidden="1"' if it["hidden"] else ""
            esc_rel = html.escape(it["rel_path"], quote=True)
            esc_raw_name = html.escape(it["name"], quote=True)
            rows_html.append(
                f'<tr class="item-row"{hidden_attr} '
                f'data-isdir="{it["is_dir"]}" '
                f'data-editable="{it["editable"]}" '
                f'data-extractable="{it["extractable"]}" '
                f'data-preview="{it["preview"]}" '
                f'data-href="{html.escape(it["href"], quote=True)}" '
                f'data-name="{html.escape(it["name"].lower(), quote=True)}" '
                f'data-rawname="{esc_raw_name}" '
                f'data-path="{esc_rel}" '
                f'data-size="{it["size"]}" '
                f'data-mtime="{it["mtime"]:.0f}">'
                f'<td class="col-check">'
                f'<input type="checkbox" class="row-check" value="{esc_rel}" aria-label="Select {esc_raw_name}">'
                f"</td>"
                f'<td class="col-name">'
                f'<a href="{it["href"]}" class="row-link {it["css_class"]}">'
                f'<span class="badge badge-{it["css_class"]}">{it["badge"]}</span>'
                f'<span class="fname">{html.escape(it["display_name"])}</span>'
                f"</a></td>"
                f'<td class="col-size">{it["size_str"]}</td>'
                f'<td class="col-date">{it["mtime_str"]}</td>'
                f"</tr>"
            )

        rows_str = "\n".join(rows_html)
        enc = sys.getfilesystemencoding()
        title = html.escape(url_path)
        current_dir_js = json.dumps(url_path)

        # Storage usage calculation for the current directory's filesystem
        try:
            usage = shutil.disk_usage(path)
            free_str = human_size(usage.free)
            total_str = human_size(usage.total)
            used_str = human_size(usage.used)
            used_pct = (usage.used / usage.total * 100.0) if usage.total > 0 else 0.0
        except OSError:
            free_str, total_str, used_str, used_pct = "—", "—", "—", 0.0

        if used_pct >= 90:
            fill_class = "fill-high"
        elif used_pct >= 75:
            fill_class = "fill-warn"
        else:
            fill_class = "fill-ok"

        page = f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title} — Termux HTTP</title>
<style>
  :root {{
    --bg: #0c0e12;
    --surface: #131720;
    --surface-hover: #1b2230;
    --surface-selected: rgba(56, 189, 248, 0.12);
    --border: #232b3a;
    --text: #e2e8f0;
    --muted: #64748b;
    --accent: #22c55e;
    --danger: #ef4444;
    --dir: #38bdf8;
    --code: #4ade80;
    --media: #c084fc;
    --img: #f472b6;
    --pkg: #fb923c;
    --doc: #facc15;
    --link: #2dd4bf;
    --file: #cbd5e1;
  }}
  * {{ box-sizing: border-box; margin: 0; padding: 0; }}
  body {{
    background: var(--bg);
    color: var(--text);
    font-family: "JetBrains Mono", "Fira Code", "Cascadia Code", ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
    font-size: 14px;
    line-height: 1.5;
    padding-bottom: 84px;
  }}
  body.drag-over .table-wrap {{
    border-color: var(--dir);
    box-shadow: 0 0 0 2px rgba(56, 189, 248, 0.25);
  }}
  /* Sticky Top Breadcrumb + Toolbar */
  header {{
    position: sticky;
    top: 0;
    z-index: 30;
    background: rgba(12, 14, 18, 0.94);
    backdrop-filter: blur(10px);
    border-bottom: 1px solid var(--border);
    padding: 10px 16px;
  }}
  .top-inner {{
    max-width: 1100px;
    margin: 0 auto;
    display: flex;
    flex-wrap: wrap;
    align-items: center;
    justify-content: space-between;
    gap: 10px;
  }}
  .breadcrumbs {{
    display: flex;
    align-items: center;
    flex-wrap: wrap;
    gap: 4px;
    font-size: 14px;
    overflow-x: auto;
    flex: 1;
    min-width: 180px;
  }}
  .crumb {{
    color: var(--dir);
    text-decoration: none;
    padding: 3px 7px;
    border-radius: 5px;
    background: var(--surface);
    border: 1px solid var(--border);
    transition: background 0.15s, border-color 0.15s;
  }}
  .crumb:hover {{
    background: var(--surface-hover);
    border-color: var(--dir);
  }}
  .root-crumb {{
    color: var(--accent);
    font-weight: 700;
  }}
  .active-crumb {{
    color: var(--text);
    font-weight: 600;
  }}
  .crumb-sep {{
    color: var(--muted);
    user-select: none;
  }}
  .controls {{
    display: flex;
    align-items: center;
    gap: 8px;
    position: relative;
  }}
  .search-input {{
    background: var(--surface);
    color: var(--text);
    border: 1px solid var(--border);
    border-radius: 6px;
    padding: 6px 10px;
    font-family: inherit;
    font-size: 13px;
    width: 185px;
    outline: none;
  }}
  .search-input:focus {{
    border-color: var(--accent);
  }}
  .btn {{
    background: var(--surface);
    color: var(--text);
    border: 1px solid var(--border);
    border-radius: 6px;
    padding: 6px 11px;
    font-family: inherit;
    font-size: 12.5px;
    cursor: pointer;
    text-decoration: none;
    transition: border-color 0.15s, background 0.15s, color 0.15s;
    display: inline-flex;
    align-items: center;
    justify-content: center;
    gap: 6px;
    white-space: nowrap;
  }}
  .btn-icon {{
    padding: 6px 9px;
  }}
  .btn svg {{
    width: 15px;
    height: 15px;
    stroke: currentColor;
    stroke-width: 2;
    fill: none;
    stroke-linecap: round;
    stroke-linejoin: round;
    display: block;
  }}
  .btn:hover:not(:disabled) {{
    background: var(--surface-hover);
    border-color: var(--muted);
  }}
  .btn:disabled {{
    opacity: 0.4;
    cursor: not-allowed;
  }}
  .btn-primary {{
    border-color: rgba(34, 197, 94, 0.5);
    color: var(--accent);
  }}
  .btn-primary:hover:not(:disabled) {{
    border-color: var(--accent);
    background: rgba(34, 197, 94, 0.12);
  }}
  .btn-danger {{
    border-color: rgba(239, 68, 68, 0.45);
    color: var(--danger);
  }}
  .btn-danger:hover:not(:disabled) {{
    border-color: var(--danger);
    background: rgba(239, 68, 68, 0.12);
  }}
  /* Hamburger Menu */
  .menu-wrap {{
    position: relative;
  }}
  .hamburger-btn {{
    font-size: 16px;
    line-height: 1;
    padding: 6px 10px;
  }}
  .dropdown-menu {{
    display: none;
    position: absolute;
    right: 0;
    top: calc(100% + 6px);
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 8px;
    min-width: 215px;
    box-shadow: 0 10px 28px rgba(0, 0, 0, 0.65);
    padding: 6px;
    z-index: 50;
  }}
  .dropdown-menu.open {{
    display: block;
  }}
  .menu-item {{
    display: flex;
    align-items: center;
    justify-content: space-between;
    width: 100%;
    background: transparent;
    border: none;
    color: var(--text);
    font-family: inherit;
    font-size: 13px;
    padding: 8px 10px;
    border-radius: 5px;
    cursor: pointer;
    text-align: left;
  }}
  .menu-item:hover {{
    background: var(--surface-hover);
  }}
  .menu-divider {{
    height: 1px;
    background: var(--border);
    margin: 5px 0;
  }}
  .dot-indicator {{
    font-size: 11px;
    padding: 1px 6px;
    border-radius: 4px;
    background: rgba(100, 116, 139, 0.2);
    color: var(--muted);
  }}
  .dot-indicator.on {{
    background: rgba(34, 197, 94, 0.18);
    color: var(--accent);
    font-weight: 700;
  }}
  /* Clipboard Paste Banner + Action Bar */
  .sub-bars {{
    max-width: 1100px;
    margin: 10px auto 0;
    padding: 0 16px;
    display: flex;
    flex-direction: column;
    gap: 8px;
  }}
  .bar-panel {{
    display: none;
    align-items: center;
    justify-content: space-between;
    flex-wrap: wrap;
    gap: 8px;
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 8px;
    padding: 8px 12px;
  }}
  .bar-panel.visible {{
    display: flex;
  }}
  .clipboard-bar {{
    border-color: rgba(56, 189, 248, 0.45);
    background: rgba(19, 23, 32, 0.95);
  }}
  .selection-bar {{
    border-color: rgba(34, 197, 94, 0.45);
  }}
  .bar-info {{
    font-size: 13px;
    color: var(--text);
    display: flex;
    align-items: center;
    gap: 8px;
  }}
  .bar-actions {{
    display: flex;
    align-items: center;
    gap: 6px;
    flex-wrap: wrap;
  }}
  main {{
    max-width: 1100px;
    margin: 12px auto 0;
    padding: 0 16px;
  }}
  .stats-bar {{
    display: flex;
    justify-content: space-between;
    align-items: center;
    flex-wrap: wrap;
    gap: 10px;
    color: var(--muted);
    font-size: 12px;
    margin-bottom: 8px;
    padding: 0 4px;
  }}
  /* Storage Footer Bar below File List */
  .footer-bar {{
    display: flex;
    justify-content: space-between;
    align-items: center;
    flex-wrap: wrap;
    gap: 10px;
    color: var(--muted);
    font-size: 12px;
    margin-top: 10px;
    padding: 0 4px;
  }}
  .storage-info {{
    display: inline-flex;
    align-items: center;
    gap: 10px;
  }}
  .storage-meter {{
    width: 96px;
    height: 7px;
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 999px;
    overflow: hidden;
    flex-shrink: 0;
  }}
  .storage-fill {{
    height: 100%;
    border-radius: 999px;
    transition: width 0.2s ease;
  }}
  .fill-ok {{ background: var(--accent); }}
  .fill-warn {{ background: var(--pkg); }}
  .fill-high {{ background: var(--danger); }}
  .fill-neutral {{ background: var(--file); }}
  .table-wrap {{
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 8px;
    overflow: hidden;
    transition: border-color 0.15s, box-shadow 0.15s;
  }}
  table {{
    width: 100%;
    border-collapse: collapse;
    text-align: left;
  }}
  th {{
    font-size: 12px;
    text-transform: uppercase;
    letter-spacing: 0.04em;
    color: var(--muted);
    padding: 10px 12px;
    border-bottom: 1px solid var(--border);
    cursor: pointer;
    user-select: none;
    white-space: nowrap;
  }}
  /* Checkboxes hidden by default until Select Mode is activated */
  th.col-check,
  td.col-check {{
    display: none;
    width: 40px;
    text-align: center;
    padding: 0 6px 0 12px;
  }}
  th.col-check {{
    padding: 10px 6px 10px 12px;
    cursor: default;
  }}
  body.select-mode th.col-check,
  body.select-mode td.col-check {{
    display: table-cell;
  }}
  th:hover:not(.col-check) {{
    color: var(--text);
  }}
  td {{
    border-bottom: 1px solid rgba(35, 43, 58, 0.55);
    padding: 0;
  }}
  input[type="checkbox"] {{
    width: 16px;
    height: 16px;
    accent-color: var(--accent);
    cursor: pointer;
    vertical-align: middle;
  }}
  tr:last-child td {{
    border-bottom: none;
  }}
  tr:hover td {{
    background: var(--surface-hover);
  }}
  tr.selected td {{
    background: var(--surface-selected);
  }}
  .row-link {{
    display: flex;
    align-items: center;
    gap: 10px;
    padding: 9px 12px;
    text-decoration: none;
    color: var(--file);
    word-break: break-all;
  }}
  body.select-mode .row-link {{
    padding-left: 6px;
  }}
  .col-size, .col-date {{
    padding: 9px 12px;
    white-space: nowrap;
    color: var(--muted);
    font-size: 12.5px;
  }}
  .col-size {{ text-align: right; width: 110px; }}
  .col-date {{ text-align: right; width: 155px; }}
  .badge {{
    display: inline-block;
    font-size: 10.5px;
    font-weight: 700;
    padding: 1px 6px;
    border-radius: 4px;
    min-width: 46px;
    text-align: center;
    flex-shrink: 0;
    border: 1px solid transparent;
  }}
  /* Filetype Colors */
  .ft-dir .fname {{ color: var(--dir); font-weight: 600; }}
  .badge-dir, .badge-ft-dir {{ color: var(--dir); background: rgba(56, 189, 248, 0.12); border-color: rgba(56, 189, 248, 0.3); }}

  .ft-code .fname {{ color: var(--code); }}
  .badge-ft-code {{ color: var(--code); background: rgba(74, 222, 128, 0.12); border-color: rgba(74, 222, 128, 0.3); }}

  .ft-media .fname {{ color: var(--media); }}
  .badge-ft-media {{ color: var(--media); background: rgba(192, 132, 252, 0.12); border-color: rgba(192, 132, 252, 0.3); }}

  .ft-img .fname {{ color: var(--img); }}
  .badge-ft-img {{ color: var(--img); background: rgba(244, 114, 182, 0.12); border-color: rgba(244, 114, 182, 0.3); }}

  .ft-pkg .fname {{ color: var(--pkg); }}
  .badge-ft-pkg {{ color: var(--pkg); background: rgba(251, 146, 60, 0.12); border-color: rgba(251, 146, 60, 0.3); }}

  .ft-doc .fname {{ color: var(--doc); }}
  .badge-ft-doc {{ color: var(--doc); background: rgba(250, 204, 21, 0.12); border-color: rgba(250, 204, 21, 0.3); }}

  .ft-link .fname {{ color: var(--link); }}
  .badge-ft-link {{ color: var(--link); background: rgba(45, 212, 191, 0.12); border-color: rgba(45, 212, 191, 0.3); }}

  .ft-file .fname {{ color: var(--file); }}
  .badge-ft-file {{ color: var(--muted); background: rgba(100, 116, 139, 0.12); border-color: rgba(100, 116, 139, 0.25); }}

  /* Standard Modal Dialog */
  .modal-backdrop {{
    display: none;
    position: fixed;
    inset: 0;
    background: rgba(0, 0, 0, 0.76);
    z-index: 100;
    align-items: center;
    justify-content: center;
    padding: 16px;
  }}
  .modal-backdrop.open {{
    display: flex;
  }}
  .modal {{
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 10px;
    width: 100%;
    max-width: 440px;
    padding: 18px;
    box-shadow: 0 16px 40px rgba(0, 0, 0, 0.75);
  }}
  .modal-title {{
    font-size: 15px;
    font-weight: 700;
    margin-bottom: 10px;
    color: var(--text);
  }}
  .modal-desc {{
    font-size: 13px;
    color: var(--muted);
    margin-bottom: 12px;
    word-break: break-all;
  }}
  .modal-input {{
    width: 100%;
    background: var(--bg);
    color: var(--text);
    border: 1px solid var(--border);
    border-radius: 6px;
    padding: 8px 10px;
    font-family: inherit;
    font-size: 13.5px;
    margin-bottom: 12px;
    outline: none;
  }}
  .modal-input:focus {{
    border-color: var(--accent);
  }}
  .modal-check-row {{
    display: none;
    align-items: center;
    gap: 8px;
    font-size: 13px;
    color: var(--text);
    margin-bottom: 14px;
    cursor: pointer;
    user-select: none;
  }}
  .modal-check-row.visible {{
    display: flex;
  }}
  .modal-actions {{
    display: flex;
    justify-content: flex-end;
    gap: 8px;
  }}

  /* Inline Text Viewer & Editor Modal */
  .editor-modal {{
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 10px;
    width: 100%;
    max-width: 960px;
    height: min(86vh, 760px);
    display: flex;
    flex-direction: column;
    box-shadow: 0 18px 48px rgba(0, 0, 0, 0.8);
    overflow: hidden;
  }}
  .editor-header, .editor-footer {{
    padding: 10px 14px;
    background: var(--bg);
    display: flex;
    align-items: center;
    justify-content: space-between;
    gap: 10px;
    flex-wrap: wrap;
  }}
  .editor-header {{ border-bottom: 1px solid var(--border); }}
  .editor-footer {{ border-top: 1px solid var(--border); font-size: 12px; color: var(--muted); }}
  .editor-title {{
    font-weight: 700;
    color: var(--code);
    word-break: break-all;
  }}
  .editor-textarea {{
    flex: 1;
    width: 100%;
    background: #090b0f;
    color: var(--text);
    border: none;
    padding: 14px;
    font-family: inherit;
    font-size: 13.5px;
    line-height: 1.55;
    resize: none;
    outline: none;
    tab-size: 2;
  }}
  .editor-footer-left {{
    display: flex;
    align-items: center;
    gap: 12px;
    flex-wrap: wrap;
  }}
  .cursor-pos {{
    color: var(--dir);
    font-weight: 600;
  }}

  /* Lightbox Modal for Images & Media */
  .lightbox-modal {{
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 10px;
    width: 100%;
    max-width: 960px;
    max-height: 90vh;
    display: flex;
    flex-direction: column;
    overflow: hidden;
    box-shadow: 0 18px 48px rgba(0, 0, 0, 0.85);
  }}
  .lightbox-modal:fullscreen,
  .lightbox-modal.is-fullscreen {{
    max-width: 100vw;
    max-height: 100vh;
    width: 100vw;
    height: 100vh;
    border-radius: 0;
    border: none;
  }}
  .lightbox-body {{
    position: relative;
    background: #07080b;
    display: flex;
    align-items: center;
    justify-content: center;
    min-height: 280px;
    max-height: 74vh;
    flex: 1;
    padding: 12px;
    overflow: hidden;
    user-select: none;
  }}
  .lightbox-modal:fullscreen .lightbox-body,
  .lightbox-modal.is-fullscreen .lightbox-body {{
    max-height: calc(100vh - 54px);
    height: calc(100vh - 54px);
  }}
  .lightbox-body img,
  .lightbox-body video {{
    max-width: 100%;
    max-height: 70vh;
    border-radius: 6px;
    object-fit: contain;
    z-index: 1;
  }}
  .lightbox-modal:fullscreen .lightbox-body img,
  .lightbox-modal:fullscreen .lightbox-body video,
  .lightbox-modal.is-fullscreen .lightbox-body img,
  .lightbox-modal.is-fullscreen .lightbox-body video {{
    max-height: calc(100vh - 78px);
  }}
  .lightbox-body audio {{
    width: min(480px, 90%);
    z-index: 1;
  }}
  /* Left & Right Edge Tap Zones for Media Navigation */
  .edge-tap-zone {{
    position: absolute;
    top: 0;
    bottom: 56px;
    width: 22%;
    z-index: 5;
    cursor: pointer;
    display: flex;
    align-items: center;
    opacity: 0;
    transition: opacity 0.15s ease, background 0.15s ease;
    -webkit-tap-highlight-color: transparent;
  }}
  .edge-tap-zone.edge-left {{
    left: 0;
    justify-content: flex-start;
    padding-left: 14px;
    background: linear-gradient(90deg, rgba(0, 0, 0, 0.35), transparent);
  }}
  .edge-tap-zone.edge-right {{
    right: 0;
    justify-content: flex-end;
    padding-right: 14px;
    background: linear-gradient(270deg, rgba(0, 0, 0, 0.35), transparent);
  }}
  .edge-tap-zone:hover,
  .edge-tap-zone:active {{
    opacity: 1;
  }}
  .edge-chevron {{
    color: rgba(226, 232, 240, 0.75);
    font-size: 20px;
    font-weight: 700;
    background: rgba(19, 23, 32, 0.7);
    border: 1px solid var(--border);
    border-radius: 999px;
    width: 34px;
    height: 34px;
    display: flex;
    align-items: center;
    justify-content: center;
  }}

  @media (max-width: 640px) {{
    .col-date {{ display: none; }}
    .search-input {{ width: 135px; }}
  }}
</style>
</head>
<body>
<header>
  <div class="top-inner">
    <nav class="breadcrumbs" aria-label="Breadcrumb">
      {breadcrumb_bar}
    </nav>
    <div class="controls">
      <input type="search" id="filterInput" class="search-input" placeholder="Filter (/)" autocomplete="off">
      <div class="menu-wrap">
        <button type="button" id="hamburgerBtn" class="btn hamburger-btn" aria-label="Menu" title="Menu">☰</button>
        <div id="dropdownMenu" class="dropdown-menu">
          <button type="button" class="menu-item" id="menuSelectBtn">
            <span>Select</span>
            <span id="selectStateBadge" class="dot-indicator">OFF</span>
          </button>
          <button type="button" class="menu-item" id="menuUploadBtn">
            <span>+ Upload Files</span>
          </button>
          <button type="button" class="menu-item" id="menuNewFolderBtn">
            <span>+ New Folder</span>
          </button>
          <button type="button" class="menu-item" id="menuNewTxtBtn">
            <span>+ New Text File</span>
          </button>
          <div class="menu-divider"></div>
          <button type="button" class="menu-item" id="toggleDotBtn">
            <span>Show .dotfiles</span>
            <span id="dotStateBadge" class="dot-indicator">OFF</span>
          </button>
        </div>
      </div>
      <form id="uploadForm" method="POST" enctype="multipart/form-data" style="display:none">
        <input type="file" id="fileUpload" name="file" multiple>
      </form>
    </div>
  </div>
</header>

<div class="sub-bars">
  <!-- Selection Manipulation Bar (shown when Select Mode is active) -->
  <div id="selectionBar" class="bar-panel selection-bar">
    <div class="bar-info">
      <strong id="selectedCountText">0 items selected</strong>
    </div>
    <div class="bar-actions">
      <button type="button" class="btn" id="actCopyBtn" title="Copy selected to clipboard" disabled>Copy</button>
      <button type="button" class="btn" id="actMoveBtn" title="Cut selected to move" disabled>Move</button>
      <button type="button" class="btn" id="actRenameBtn" title="Rename single selected item" disabled>Rename</button>
      <button type="button" class="btn" id="actEditBtn" title="Open selected file in text editor" disabled>Edit</button>
      <button type="button" class="btn" id="actZipBtn" title="Download selected items as .zip" disabled>Zip</button>
      <button type="button" class="btn" id="actExtractBtn" title="Extract selected archive" disabled>Extract</button>
      <button type="button" class="btn btn-danger" id="actDeleteBtn" title="Delete selected items" disabled>Delete</button>
      <button type="button" class="btn" id="actExitSelectBtn" title="Exit Select Mode">Done</button>
    </div>
  </div>

  <!-- Persistent Cross-Folder Clipboard Bar -->
  <div id="clipboardBar" class="bar-panel clipboard-bar">
    <div class="bar-info">
      <span id="clipboardText">Clipboard empty</span>
    </div>
    <div class="bar-actions">
      <button type="button" class="btn btn-primary" id="pasteHereBtn">Paste Here</button>
      <button type="button" class="btn" id="clearClipboardBtn">Cancel</button>
    </div>
  </div>
</div>

<main>
  <div class="stats-bar">
    <span>{dir_count} folders, {file_count} files</span>
    <div id="uploadBar" class="storage-info" style="display:none">
      <div class="storage-meter">
        <div id="uploadFill" class="storage-fill fill-neutral" style="width: 0%"></div>
      </div>
      <span id="uploadText">0 B / 0 B (0%)</span>
    </div>
  </div>
  <div class="table-wrap">
    <table id="fileTable">
      <thead>
        <tr>
          <th class="col-check"><input type="checkbox" id="selectAllCheck" title="Select all visible"></th>
          <th data-sort="name">Name ▲</th>
          <th data-sort="size" class="col-size">Size</th>
          <th data-sort="mtime" class="col-date">Modified</th>
        </tr>
      </thead>
      <tbody id="fileBody">
        {rows_str}
      </tbody>
    </table>
  </div>
  <div class="footer-bar">
    <div class="storage-info" title="{used_str} used ({used_pct:.1f}%)">
      <div class="storage-meter">
        <div class="storage-fill {fill_class}" style="width: {min(max(used_pct, 0.0), 100.0):.1f}%"></div>
      </div>
      <span>{free_str} free / {total_str} total ({used_pct:.0f}% used)</span>
    </div>
  </div>
</main>

<!-- Modal for Rename / New Folder / New Text File / Delete Confirm -->
<div id="modalBackdrop" class="modal-backdrop">
  <div class="modal">
    <div id="modalTitle" class="modal-title">Action</div>
    <div id="modalDesc" class="modal-desc"></div>
    <input type="text" id="modalInput" class="modal-input" autocomplete="off">
    <label id="modalCheckRow" class="modal-check-row">
      <input type="checkbox" id="modalExtraCheck" checked>
      <span id="modalCheckLabel">Open in editor after creation</span>
    </label>
    <div class="modal-actions">
      <button type="button" class="btn" id="modalCancelBtn">Cancel</button>
      <button type="button" class="btn btn-primary" id="modalConfirmBtn">Confirm</button>
    </div>
  </div>
</div>

<!-- Modal for Inline Text Viewer & Editor -->
<div id="editorBackdrop" class="modal-backdrop">
  <div class="editor-modal">
    <div class="editor-header">
      <span id="editorTitle" class="editor-title">file.txt</span>
      <div class="bar-actions">
        <a id="editorOpenLink" href="#" target="_blank" rel="noopener" class="btn" title="Open file directly in browser">Open</a>
        <a id="editorRawLink" href="#" download class="btn btn-icon" title="Download file" aria-label="Download file">
          <svg viewBox="0 0 24 24"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>
        </a>
        <button type="button" id="editorSaveBtn" class="btn btn-primary">Save</button>
        <button type="button" id="editorCloseBtn" class="btn">Close</button>
      </div>
    </div>
    <textarea id="editorTextarea" class="editor-textarea" spellcheck="false"></textarea>
    <div class="editor-footer">
      <div class="editor-footer-left">
        <span id="editorCursorPos" class="cursor-pos">Ln 1, Col 1</span>
        <span id="editorStats">0 lines, 0 chars</span>
      </div>
      <span id="editorStatus">Ctrl+S to save</span>
    </div>
  </div>
</div>

<!-- Modal for Image & Media Lightbox -->
<div id="lightboxBackdrop" class="modal-backdrop">
  <div id="lightboxModal" class="lightbox-modal">
    <div class="editor-header">
      <span id="lightboxTitle" class="editor-title">preview</span>
      <div class="bar-actions">
        <button type="button" id="lightboxPrevBtn" class="btn" title="Previous media">◀ Prev</button>
        <a id="lightboxOpenLink" href="#" target="_blank" rel="noopener" class="btn" title="Open media directly in browser">Open</a>
        <button type="button" id="lightboxNextBtn" class="btn" title="Next media">Next ▶</button>
        <a id="lightboxDownloadLink" href="#" download class="btn btn-icon" title="Download file" aria-label="Download file">
          <svg viewBox="0 0 24 24"><path d="M21 15v4a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2v-4"/><polyline points="7 10 12 15 17 10"/><line x1="12" y1="15" x2="12" y2="3"/></svg>
        </a>
        <button type="button" id="lightboxFullscreenBtn" class="btn btn-icon" title="Toggle Fullscreen" aria-label="Toggle Fullscreen">
          <svg viewBox="0 0 24 24"><polyline points="15 3 21 3 21 9"/><polyline points="9 21 3 21 3 15"/><line x1="21" y1="3" x2="14" y2="10"/><line x1="3" y1="21" x2="10" y2="14"/></svg>
        </button>
        <button type="button" id="lightboxCloseBtn" class="btn" title="Close">✕</button>
      </div>
    </div>
    <div id="lightboxBody" class="lightbox-body">
      <div id="edgeTapLeft" class="edge-tap-zone edge-left" title="Previous">
        <span class="edge-chevron">‹</span>
      </div>
      <div id="lightboxMediaSlot"></div>
      <div id="edgeTapRight" class="edge-tap-zone edge-right" title="Next">
        <span class="edge-chevron">›</span>
      </div>
    </div>
  </div>
</div>

<script>
(() => {{
  const CURRENT_DIR = {current_dir_js};
  const CLIPBOARD_KEY = 'termux_http_clipboard_v1';
  const DOTFILES_KEY = 'termux_http_dotfiles_v2';

  const filterInput = document.getElementById('filterInput');
  const hamburgerBtn = document.getElementById('hamburgerBtn');
  const dropdownMenu = document.getElementById('dropdownMenu');
  const menuSelectBtn = document.getElementById('menuSelectBtn');
  const selectStateBadge = document.getElementById('selectStateBadge');
  const menuUploadBtn = document.getElementById('menuUploadBtn');
  const menuNewFolderBtn = document.getElementById('menuNewFolderBtn');
  const menuNewTxtBtn = document.getElementById('menuNewTxtBtn');
  const fileUpload = document.getElementById('fileUpload');
  const uploadForm = document.getElementById('uploadForm');
  const toggleDotBtn = document.getElementById('toggleDotBtn');
  const dotStateBadge = document.getElementById('dotStateBadge');

  const uploadBar = document.getElementById('uploadBar');
  const uploadFill = document.getElementById('uploadFill');
  const uploadText = document.getElementById('uploadText');

  const tbody = document.getElementById('fileBody');
  const rows = Array.from(tbody.querySelectorAll('.item-row'));
  const headers = Array.from(document.querySelectorAll('th[data-sort]'));
  const selectAllCheck = document.getElementById('selectAllCheck');

  const selectionBar = document.getElementById('selectionBar');
  const selectedCountText = document.getElementById('selectedCountText');
  const actCopyBtn = document.getElementById('actCopyBtn');
  const actMoveBtn = document.getElementById('actMoveBtn');
  const actRenameBtn = document.getElementById('actRenameBtn');
  const actEditBtn = document.getElementById('actEditBtn');
  const actZipBtn = document.getElementById('actZipBtn');
  const actExtractBtn = document.getElementById('actExtractBtn');
  const actDeleteBtn = document.getElementById('actDeleteBtn');
  const actExitSelectBtn = document.getElementById('actExitSelectBtn');

  const clipboardBar = document.getElementById('clipboardBar');
  const clipboardText = document.getElementById('clipboardText');
  const pasteHereBtn = document.getElementById('pasteHereBtn');
  const clearClipboardBtn = document.getElementById('clearClipboardBtn');

  const modalBackdrop = document.getElementById('modalBackdrop');
  const modalTitle = document.getElementById('modalTitle');
  const modalDesc = document.getElementById('modalDesc');
  const modalInput = document.getElementById('modalInput');
  const modalCheckRow = document.getElementById('modalCheckRow');
  const modalExtraCheck = document.getElementById('modalExtraCheck');
  const modalCheckLabel = document.getElementById('modalCheckLabel');
  const modalCancelBtn = document.getElementById('modalCancelBtn');
  const modalConfirmBtn = document.getElementById('modalConfirmBtn');

  const editorBackdrop = document.getElementById('editorBackdrop');
  const editorTitle = document.getElementById('editorTitle');
  const editorOpenLink = document.getElementById('editorOpenLink');
  const editorRawLink = document.getElementById('editorRawLink');
  const editorSaveBtn = document.getElementById('editorSaveBtn');
  const editorCloseBtn = document.getElementById('editorCloseBtn');
  const editorTextarea = document.getElementById('editorTextarea');
  const editorCursorPos = document.getElementById('editorCursorPos');
  const editorStats = document.getElementById('editorStats');
  const editorStatus = document.getElementById('editorStatus');

  const lightboxBackdrop = document.getElementById('lightboxBackdrop');
  const lightboxModal = document.getElementById('lightboxModal');
  const lightboxTitle = document.getElementById('lightboxTitle');
  const lightboxBody = document.getElementById('lightboxBody');
  const lightboxMediaSlot = document.getElementById('lightboxMediaSlot');
  const edgeTapLeft = document.getElementById('edgeTapLeft');
  const edgeTapRight = document.getElementById('edgeTapRight');
  const lightboxPrevBtn = document.getElementById('lightboxPrevBtn');
  const lightboxOpenLink = document.getElementById('lightboxOpenLink');
  const lightboxNextBtn = document.getElementById('lightboxNextBtn');
  const lightboxDownloadLink = document.getElementById('lightboxDownloadLink');
  const lightboxFullscreenBtn = document.getElementById('lightboxFullscreenBtn');
  const lightboxCloseBtn = document.getElementById('lightboxCloseBtn');

  // .dotfiles OFF by default
  let showDotfiles = localStorage.getItem(DOTFILES_KEY) === '1';
  let selectMode = false;
  let sortKey = 'name';
  let sortAsc = true;
  let modalHandler = null;

  let currentEditorPath = null;
  let editorDirty = false;
  let editorReloadOnClose = false;

  let lightboxItems = [];
  let lightboxIndex = -1;

  function formatBytes(b) {{
    const units = ['B', 'KB', 'MB', 'GB', 'TB'];
    let i = 0;
    while (b >= 1024 && i < units.length - 1) {{ b /= 1024; i++; }}
    return (i === 0 ? b.toFixed(0) : b.toFixed(1)) + ' ' + units[i];
  }}

  // Hamburger menu logic
  hamburgerBtn.addEventListener('click', (e) => {{
    e.stopPropagation();
    dropdownMenu.classList.toggle('open');
  }});
  document.addEventListener('click', (e) => {{
    if (!dropdownMenu.contains(e.target) && e.target !== hamburgerBtn) {{
      dropdownMenu.classList.remove('open');
    }}
  }});

  // Select Mode toggle
  function setSelectMode(enabled) {{
    selectMode = Boolean(enabled);
    document.body.classList.toggle('select-mode', selectMode);
    selectionBar.classList.toggle('visible', selectMode);
    selectStateBadge.textContent = selectMode ? 'ON' : 'OFF';
    selectStateBadge.classList.toggle('on', selectMode);
    if (!selectMode) {{
      rows.forEach(r => {{
        const cb = r.querySelector('.row-check');
        if (cb) cb.checked = false;
      }});
    }}
    updateSelectionUI();
  }}

  menuSelectBtn.addEventListener('click', () => {{
    dropdownMenu.classList.remove('open');
    setSelectMode(!selectMode);
  }});

  actExitSelectBtn.addEventListener('click', () => {{
    setSelectMode(false);
  }});

  // Upload files with top progress bar (via button or drag & drop)
  function uploadFileList(files) {{
    if (!files || !files.length) return;
    const formData = new FormData();
    for (const f of files) {{
      formData.append('file', f);
    }}
    const xhr = new XMLHttpRequest();
    uploadBar.style.display = 'inline-flex';
    uploadFill.style.width = '0%';
    uploadText.textContent = 'Uploading...';

    xhr.upload.addEventListener('progress', (e) => {{
      if (!e.lengthComputable) return;
      const pct = Math.min(100, Math.round((e.loaded / e.total) * 100));
      uploadFill.style.width = `${{pct}}%`;
      uploadText.textContent = `${{formatBytes(e.loaded)}} / ${{formatBytes(e.total)}} (${{pct}}%)`;
    }});

    xhr.addEventListener('load', () => {{
      if (xhr.status >= 200 && xhr.status < 400) {{
        window.location.reload();
      }} else {{
        alert('Upload failed');
        uploadBar.style.display = 'none';
      }}
    }});

    xhr.addEventListener('error', () => {{
      alert('Upload error');
      uploadBar.style.display = 'none';
    }});

    xhr.open('POST', window.location.pathname);
    xhr.send(formData);
  }}

  menuUploadBtn.addEventListener('click', () => {{
    dropdownMenu.classList.remove('open');
    fileUpload.click();
  }});
  fileUpload.addEventListener('change', () => {{
    if (fileUpload.files.length > 0) uploadFileList(fileUpload.files);
  }});

  // Drag & Drop upload anywhere on window
  let dragCounter = 0;
  window.addEventListener('dragenter', (e) => {{
    if (e.dataTransfer && Array.from(e.dataTransfer.types).includes('Files')) {{
      e.preventDefault();
      dragCounter++;
      document.body.classList.add('drag-over');
    }}
  }});
  window.addEventListener('dragover', (e) => {{
    if (e.dataTransfer && Array.from(e.dataTransfer.types).includes('Files')) {{
      e.preventDefault();
    }}
  }});
  window.addEventListener('dragleave', () => {{
    dragCounter = Math.max(0, dragCounter - 1);
    if (dragCounter === 0) document.body.classList.remove('drag-over');
  }});
  window.addEventListener('drop', (e) => {{
    dragCounter = 0;
    document.body.classList.remove('drag-over');
    if (e.dataTransfer && e.dataTransfer.files && e.dataTransfer.files.length > 0) {{
      e.preventDefault();
      uploadFileList(e.dataTransfer.files);
    }}
  }});

  function syncDotfilesUI() {{
    dotStateBadge.textContent = showDotfiles ? 'ON' : 'OFF';
    dotStateBadge.classList.toggle('on', showDotfiles);
  }}

  function applyFilter() {{
    const q = filterInput.value.trim().toLowerCase();
    for (const r of rows) {{
      const isHidden = r.dataset.hidden === '1';
      const name = r.dataset.name || '';
      const matchDot = showDotfiles || !isHidden;
      const matchQuery = !q || name.includes(q);
      const visible = matchDot && matchQuery;
      r.style.display = visible ? '' : 'none';
    }}
    updateSelectionUI();
  }}

  toggleDotBtn.addEventListener('click', () => {{
    showDotfiles = !showDotfiles;
    localStorage.setItem(DOTFILES_KEY, showDotfiles ? '1' : '0');
    syncDotfilesUI();
    applyFilter();
  }});

  filterInput.addEventListener('input', applyFilter);

  // Selection logic
  function getVisibleRows() {{
    return rows.filter(r => r.style.display !== 'none');
  }}

  function getSelectedRows() {{
    return rows.filter(r => {{
      const cb = r.querySelector('.row-check');
      return cb && cb.checked;
    }});
  }}

  function updateSelectionUI() {{
    const selected = getSelectedRows();
    const visible = getVisibleRows();
    rows.forEach(r => {{
      const cb = r.querySelector('.row-check');
      r.classList.toggle('selected', Boolean(selectMode && cb && cb.checked));
    }});
    const count = selected.length;
    selectedCountText.textContent = `${{count}} item${{count === 1 ? '' : 's'}} selected`;
    actCopyBtn.disabled = count === 0;
    actMoveBtn.disabled = count === 0;
    actZipBtn.disabled = count === 0;
    actDeleteBtn.disabled = count === 0;
    actRenameBtn.disabled = count !== 1;
    actEditBtn.disabled = !(count === 1 && selected[0].dataset.isdir === '0');
    actExtractBtn.disabled = !(count === 1 && selected[0].dataset.extractable === '1');
    selectAllCheck.checked = visible.length > 0 && visible.every(r => r.querySelector('.row-check').checked);
    selectAllCheck.indeterminate = count > 0 && !selectAllCheck.checked;
  }}

  rows.forEach(r => {{
    const cb = r.querySelector('.row-check');
    const link = r.querySelector('.row-link');
    cb.addEventListener('change', updateSelectionUI);
    link.addEventListener('click', (e) => {{
      if (selectMode) {{
        e.preventDefault();
        cb.checked = !cb.checked;
        updateSelectionUI();
        return;
      }}
      // Normal mode: intercept text/code files for inline editor, and images/media for lightbox
      if (r.dataset.editable === '1') {{
        e.preventDefault();
        openEditor(r.dataset.path, r.dataset.rawname, r.dataset.href, false);
      }} else if (r.dataset.preview) {{
        e.preventDefault();
        openLightboxForRow(r);
      }}
    }});
  }});

  selectAllCheck.addEventListener('change', () => {{
    const checked = selectAllCheck.checked;
    getVisibleRows().forEach(r => {{
      r.querySelector('.row-check').checked = checked;
    }});
    updateSelectionUI();
  }});

  // Clipboard state (Copy / Move across folders)
  function getClipboard() {{
    try {{
      const raw = sessionStorage.getItem(CLIPBOARD_KEY);
      return raw ? JSON.parse(raw) : null;
    }} catch {{
      return null;
    }}
  }}

  function setClipboard(mode, items) {{
    sessionStorage.setItem(CLIPBOARD_KEY, JSON.stringify({{ mode, items }}));
    renderClipboardBar();
  }}

  function clearClipboard() {{
    sessionStorage.removeItem(CLIPBOARD_KEY);
    renderClipboardBar();
  }}

  function renderClipboardBar() {{
    const clip = getClipboard();
    if (!clip || !Array.isArray(clip.items) || clip.items.length === 0) {{
      clipboardBar.classList.remove('visible');
      return;
    }}
    const verb = clip.mode === 'move' ? 'queued to move' : 'copied';
    clipboardText.textContent = `${{clip.items.length}} item(s) ${{verb}} — navigate to target folder and tap Paste Here`;
    pasteHereBtn.textContent = clip.mode === 'move' ? 'Move Here' : 'Paste Here';
    clipboardBar.classList.add('visible');
  }}

  actCopyBtn.addEventListener('click', () => {{
    const paths = getSelectedRows().map(r => r.dataset.path);
    if (!paths.length) return;
    setClipboard('copy', paths);
    setSelectMode(false);
  }});

  actMoveBtn.addEventListener('click', () => {{
    const paths = getSelectedRows().map(r => r.dataset.path);
    if (!paths.length) return;
    setClipboard('move', paths);
    setSelectMode(false);
  }});

  clearClipboardBtn.addEventListener('click', clearClipboard);

  async function apiCall(payload) {{
    const res = await fetch(window.location.pathname, {{
      method: 'POST',
      headers: {{ 'Content-Type': 'application/json' }},
      body: JSON.stringify(payload),
    }});
    const data = await res.json();
    if (!res.ok || !data.ok) {{
      throw new Error(data.error || 'Operation failed');
    }}
    return data;
  }}

  pasteHereBtn.addEventListener('click', async () => {{
    const clip = getClipboard();
    if (!clip || !clip.items.length) return;
    pasteHereBtn.disabled = true;
    try {{
      await apiCall({{
        action: clip.mode,
        items: clip.items,
        dest_dir: CURRENT_DIR,
      }});
      clearClipboard();
      window.location.reload();
    }} catch (err) {{
      alert(err.message);
      pasteHereBtn.disabled = false;
    }}
  }});

  // Zip download action
  actZipBtn.addEventListener('click', () => {{
    const paths = getSelectedRows().map(r => r.dataset.path);
    if (!paths.length) return;
    const params = new URLSearchParams({{ action: 'zip' }});
    paths.forEach(p => params.append('item', p));
    window.location.href = `${{window.location.pathname}}?${{params.toString()}}`;
    setSelectMode(false);
  }});

  // Archive extract action
  actExtractBtn.addEventListener('click', async () => {{
    const sel = getSelectedRows();
    if (sel.length !== 1) return;
    actExtractBtn.disabled = true;
    try {{
      await apiCall({{ action: 'extract', src: sel[0].dataset.path }});
      window.location.reload();
    }} catch (err) {{
      alert(err.message);
      actExtractBtn.disabled = false;
    }}
  }});

  // Edit button in Select Bar
  actEditBtn.addEventListener('click', () => {{
    const sel = getSelectedRows();
    if (sel.length !== 1) return;
    const r = sel[0];
    setSelectMode(false);
    openEditor(r.dataset.path, r.dataset.rawname, r.dataset.href, false);
  }});

  // Inline Text Viewer / Editor functions
  function updateEditorStats() {{
    const val = editorTextarea.value;
    const lines = val ? val.split('\\n').length : 1;
    editorStats.textContent = `${{lines}} line${{lines === 1 ? '' : 's'}}, ${{val.length}} chars`;
    updateEditorCursorPos();
  }}

  function updateEditorCursorPos() {{
    const val = editorTextarea.value;
    const start = editorTextarea.selectionStart || 0;
    const end = editorTextarea.selectionEnd || 0;
    const upToStart = val.slice(0, start).split('\\n');
    const startLine = upToStart.length;
    const startCol = upToStart[upToStart.length - 1].length + 1;

    if (end > start) {{
      const upToEnd = val.slice(0, end).split('\\n');
      const endLine = upToEnd.length;
      if (endLine !== startLine) {{
        editorCursorPos.textContent = `Ln ${{startLine}}–${{endLine}} (${{endLine - startLine + 1}} lines selected)`;
        return;
      }}
      editorCursorPos.textContent = `Ln ${{startLine}}, Col ${{startCol}} (${{end - start}} selected)`;
      return;
    }}
    editorCursorPos.textContent = `Ln ${{startLine}}, Col ${{startCol}}`;
  }}

  async function openEditor(relPath, displayName, rawHref, reloadOnClose) {{
    try {{
      const data = await apiCall({{ action: 'read_text', path: relPath }});
      currentEditorPath = relPath;
      editorReloadOnClose = Boolean(reloadOnClose);
      editorDirty = false;
      const targetHref = rawHref || encodeURIComponent(data.name);
      editorTitle.textContent = data.name || displayName;
      editorOpenLink.href = targetHref;
      editorRawLink.href = targetHref;
      editorTextarea.value = data.content || '';
      editorTextarea.setSelectionRange(0, 0);
      editorStatus.textContent = 'Ctrl+S to save';
      updateEditorStats();
      editorBackdrop.classList.add('open');
      setTimeout(() => {{
        editorTextarea.focus();
        updateEditorCursorPos();
      }}, 20);
    }} catch (err) {{
      alert(err.message);
    }}
  }}

  async function saveEditorContent() {{
    if (!currentEditorPath) return;
    editorSaveBtn.disabled = true;
    editorStatus.textContent = 'Saving...';
    try {{
      await apiCall({{
        action: 'write_text',
        path: currentEditorPath,
        content: editorTextarea.value,
      }});
      editorDirty = false;
      editorReloadOnClose = true;
      editorTitle.textContent = editorTitle.textContent.replace(/\\*$/, '');
      editorStatus.textContent = 'Saved ✓';
    }} catch (err) {{
      alert(err.message);
      editorStatus.textContent = 'Save failed';
    }} finally {{
      editorSaveBtn.disabled = false;
    }}
  }}

  function closeEditor() {{
    if (editorDirty && !confirm('Discard unsaved changes?')) return;
    editorBackdrop.classList.remove('open');
    currentEditorPath = null;
    if (editorReloadOnClose) {{
      window.location.reload();
    }}
  }}

  editorTextarea.addEventListener('input', () => {{
    if (!editorDirty) {{
      editorDirty = true;
      if (!editorTitle.textContent.endsWith('*')) {{
        editorTitle.textContent += '*';
      }}
    }}
    editorStatus.textContent = 'Unsaved changes';
    updateEditorStats();
  }});

  ['click', 'keyup', 'select', 'focus'].forEach(evt => {{
    editorTextarea.addEventListener(evt, updateEditorCursorPos);
  }});

  editorTextarea.addEventListener('keydown', (e) => {{
    if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 's') {{
      e.preventDefault();
      saveEditorContent();
    }} else if (e.key === 'Tab') {{
      e.preventDefault();
      const start = editorTextarea.selectionStart;
      const end = editorTextarea.selectionEnd;
      editorTextarea.setRangeText('  ', start, end, 'end');
      editorTextarea.dispatchEvent(new Event('input'));
    }}
  }});

  editorSaveBtn.addEventListener('click', saveEditorContent);
  editorCloseBtn.addEventListener('click', closeEditor);
  editorBackdrop.addEventListener('click', (e) => {{
    if (e.target === editorBackdrop) closeEditor();
  }});

  // Lightbox functions (Images, Video, Audio)
  function openLightboxForRow(targetRow) {{
    lightboxItems = getVisibleRows().filter(r => Boolean(r.dataset.preview));
    lightboxIndex = lightboxItems.indexOf(targetRow);
    if (lightboxIndex === -1) return;
    renderLightboxItem();
    lightboxBackdrop.classList.add('open');
  }}

  function renderLightboxItem() {{
    if (lightboxIndex < 0 || lightboxIndex >= lightboxItems.length) return;
    const r = lightboxItems[lightboxIndex];
    const kind = r.dataset.preview;
    const href = r.dataset.href;
    const name = r.dataset.rawname;
    const hasMultiple = lightboxItems.length > 1;

    lightboxTitle.textContent = `${{name}} (${{lightboxIndex + 1}}/${{lightboxItems.length}})`;
    lightboxOpenLink.href = href;
    lightboxDownloadLink.href = href;
    lightboxPrevBtn.disabled = !hasMultiple;
    lightboxNextBtn.disabled = !hasMultiple;
    edgeTapLeft.style.display = hasMultiple ? 'flex' : 'none';
    edgeTapRight.style.display = hasMultiple ? 'flex' : 'none';
    lightboxMediaSlot.innerHTML = '';

    if (kind === 'image') {{
      const img = document.createElement('img');
      img.src = href;
      img.alt = name;
      lightboxMediaSlot.appendChild(img);
    }} else if (kind === 'video') {{
      const vid = document.createElement('video');
      vid.src = href;
      vid.controls = true;
      vid.autoplay = true;
      lightboxMediaSlot.appendChild(vid);
    }} else if (kind === 'audio') {{
      const aud = document.createElement('audio');
      aud.src = href;
      aud.controls = true;
      aud.autoplay = true;
      lightboxMediaSlot.appendChild(aud);
    }}
  }}

  async function toggleLightboxFullscreen() {{
    if (document.fullscreenElement) {{
      try {{ await document.exitFullscreen(); }} catch {{}}
      lightboxModal.classList.remove('is-fullscreen');
      return;
    }}
    if (lightboxModal.requestFullscreen) {{
      try {{
        await lightboxModal.requestFullscreen();
        return;
      }} catch {{}}
    }}
    lightboxModal.classList.toggle('is-fullscreen');
  }}

  function closeLightbox() {{
    if (document.fullscreenElement) {{
      try {{ document.exitFullscreen(); }} catch {{}}
    }}
    lightboxModal.classList.remove('is-fullscreen');
    lightboxMediaSlot.innerHTML = '';
    lightboxBackdrop.classList.remove('open');
    lightboxIndex = -1;
  }}

  function stepLightbox(delta) {{
    if (lightboxItems.length <= 1) return;
    lightboxIndex = (lightboxIndex + delta + lightboxItems.length) % lightboxItems.length;
    renderLightboxItem();
  }}

  lightboxPrevBtn.addEventListener('click', () => stepLightbox(-1));
  lightboxNextBtn.addEventListener('click', () => stepLightbox(1));
  edgeTapLeft.addEventListener('click', (e) => {{
    e.stopPropagation();
    stepLightbox(-1);
  }});
  edgeTapRight.addEventListener('click', (e) => {{
    e.stopPropagation();
    stepLightbox(1);
  }});
  lightboxFullscreenBtn.addEventListener('click', toggleLightboxFullscreen);
  lightboxCloseBtn.addEventListener('click', closeLightbox);
  lightboxBackdrop.addEventListener('click', (e) => {{
    if (e.target === lightboxBackdrop) closeLightbox();
  }});

  // Modal helpers (Rename, New Folder, New Text File, Delete)
  function openModal({{
    title,
    desc,
    defaultValue = '',
    showInput = true,
    showCheckbox = false,
    checkboxLabel = 'Open in editor after creation',
    checkboxDefault = true,
    danger = false,
    confirmLabel = 'Confirm',
    onConfirm,
  }}) {{
    modalTitle.textContent = title;
    modalDesc.textContent = desc;
    modalInput.style.display = showInput ? 'block' : 'none';
    modalInput.value = defaultValue;
    modalCheckRow.classList.toggle('visible', Boolean(showCheckbox));
    modalCheckLabel.textContent = checkboxLabel;
    modalExtraCheck.checked = Boolean(checkboxDefault);
    modalConfirmBtn.textContent = confirmLabel;
    modalConfirmBtn.className = danger ? 'btn btn-danger' : 'btn btn-primary';
    modalHandler = onConfirm;
    modalBackdrop.classList.add('open');
    if (showInput) {{
      setTimeout(() => {{
        modalInput.focus();
        const dotIdx = defaultValue.lastIndexOf('.');
        if (dotIdx > 0) {{
          modalInput.setSelectionRange(0, dotIdx);
        }} else {{
          modalInput.select();
        }}
      }}, 20);
    }}
  }}

  function closeModal() {{
    modalBackdrop.classList.remove('open');
    modalHandler = null;
  }}

  modalCancelBtn.addEventListener('click', closeModal);
  modalBackdrop.addEventListener('click', (e) => {{
    if (e.target === modalBackdrop) closeModal();
  }});
  modalConfirmBtn.addEventListener('click', async () => {{
    if (!modalHandler) return;
    modalConfirmBtn.disabled = true;
    try {{
      const shouldReload = await modalHandler(modalInput.value.trim(), modalExtraCheck.checked);
      closeModal();
      if (shouldReload !== false) {{
        window.location.reload();
      }}
    }} catch (err) {{
      alert(err.message);
    }} finally {{
      modalConfirmBtn.disabled = false;
    }}
  }});
  modalInput.addEventListener('keydown', (e) => {{
    if (e.key === 'Enter') {{
      e.preventDefault();
      modalConfirmBtn.click();
    }} else if (e.key === 'Escape') {{
      closeModal();
    }}
  }});

  // Rename action
  actRenameBtn.addEventListener('click', () => {{
    const sel = getSelectedRows();
    if (sel.length !== 1) return;
    const row = sel[0];
    const oldName = row.dataset.rawname;
    const srcPath = row.dataset.path;
    openModal({{
      title: 'Rename Item',
      desc: `Enter a new name for "${{oldName}}":`,
      defaultValue: oldName,
      showInput: true,
      confirmLabel: 'Rename',
      onConfirm: async (newName) => {{
        if (!newName || newName === oldName) return false;
        await apiCall({{ action: 'rename', src: srcPath, new_name: newName }});
      }},
    }});
  }});

  // Delete action
  actDeleteBtn.addEventListener('click', () => {{
    const sel = getSelectedRows();
    if (!sel.length) return;
    const names = sel.map(r => r.dataset.rawname).slice(0, 5).join(', ');
    const more = sel.length > 5 ? ` and ${{sel.length - 5}} more` : '';
    openModal({{
      title: `Delete ${{sel.length}} Item${{sel.length === 1 ? '' : 's'}}?`,
      desc: `Permanently delete ${{names}}${{more}}? This cannot be undone.`,
      showInput: false,
      danger: true,
      confirmLabel: 'Delete',
      onConfirm: async () => {{
        await apiCall({{ action: 'delete', items: sel.map(r => r.dataset.path) }});
      }},
    }});
  }});

  // New Folder action inside hamburger menu
  menuNewFolderBtn.addEventListener('click', () => {{
    dropdownMenu.classList.remove('open');
    openModal({{
      title: 'New Folder',
      desc: `Create a folder inside ${{CURRENT_DIR}}:`,
      defaultValue: '',
      showInput: true,
      confirmLabel: 'Create',
      onConfirm: async (folderName) => {{
        if (!folderName) throw new Error('Folder name is required');
        await apiCall({{ action: 'mkdir', dir: CURRENT_DIR, name: folderName }});
      }},
    }});
  }});

  // New Text File action inside hamburger menu (with "Open in editor" checkbox ON by default)
  menuNewTxtBtn.addEventListener('click', () => {{
    dropdownMenu.classList.remove('open');
    openModal({{
      title: 'New Text File',
      desc: `Enter file name (defaults to .txt if no extension is given):`,
      defaultValue: 'untitled.txt',
      showInput: true,
      showCheckbox: true,
      checkboxLabel: 'Open in editor after creation',
      checkboxDefault: true,
      confirmLabel: 'Create',
      onConfirm: async (rawName, openAfter) => {{
        if (!rawName) throw new Error('File name is required');
        const res = await apiCall({{ action: 'touch', dir: CURRENT_DIR, name: rawName }});
        if (openAfter) {{
          await openEditor(res.path, res.name, encodeURIComponent(res.name), true);
          return false; // Wait until editor closes to reload list
        }}
        return true;
      }},
    }});
  }});

  // Keyboard shortcuts
  window.addEventListener('keydown', (e) => {{
    if (editorBackdrop.classList.contains('open')) {{
      if (e.key === 'Escape') closeEditor();
      return;
    }}
    if (lightboxBackdrop.classList.contains('open')) {{
      if (e.key === 'Escape') closeLightbox();
      else if (e.key === 'ArrowLeft') stepLightbox(-1);
      else if (e.key === 'ArrowRight') stepLightbox(1);
      else if (e.key.toLowerCase() === 'f') toggleLightboxFullscreen();
      return;
    }}
    if (modalBackdrop.classList.contains('open')) return;
    if (e.key === '/' && document.activeElement !== filterInput) {{
      e.preventDefault();
      filterInput.focus();
    }} else if (e.key === 'Escape') {{
      if (document.activeElement === filterInput) {{
        filterInput.value = '';
        filterInput.blur();
        applyFilter();
      }} else if (dropdownMenu.classList.contains('open')) {{
        dropdownMenu.classList.remove('open');
      }} else if (selectMode) {{
        setSelectMode(false);
      }}
    }}
  }});

  // Sorting
  headers.forEach(th => {{
    th.addEventListener('click', () => {{
      const key = th.dataset.sort;
      if (sortKey === key) {{
        sortAsc = !sortAsc;
      }} else {{
        sortKey = key;
        sortAsc = key === 'name';
      }}
      headers.forEach(h => {{
        const base = h.textContent.replace(/[▲▼]/g, '').trim();
        h.textContent = h === th ? `${{base}} ${{sortAsc ? '▲' : '▼'}}` : base;
      }});
      rows.sort((a, b) => {{
        const dirDiff = Number(b.dataset.isdir) - Number(a.dataset.isdir);
        if (dirDiff !== 0) return dirDiff;
        if (sortKey === 'name') {{
          return sortAsc
            ? a.dataset.name.localeCompare(b.dataset.name)
            : b.dataset.name.localeCompare(a.dataset.name);
        }}
        const va = Number(a.dataset[sortKey]);
        const vb = Number(b.dataset[sortKey]);
        return sortAsc ? va - vb : vb - va;
      }});
      rows.forEach(r => tbody.appendChild(r));
    }});
  }});

  // Initialize state
  syncDotfilesUI();
  applyFilter();
  renderClipboardBar();
}})();
</script>
</body>
</html>"""

        encoded = page.encode(enc, "surrogateescape")
        f = io.BytesIO()
        f.write(encoded)
        f.seek(0)
        self.send_response(HTTPStatus.OK)
        self.send_header("Content-Type", f"text/html; charset={enc}")
        self.send_header("Content-Length", str(len(encoded)))
        self.end_headers()
        return f


def get_lan_ip() -> str:
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s:
            s.connect(("8.8.8.8", 80))
            return s.getsockname()[0]
    except Exception:
        return "127.0.0.1"


def main():
    global SERVER_ROOT, SERVER_AUTH_TOKEN
    parser = argparse.ArgumentParser(description="Termux Dark Minimalist HTTP File Server")
    parser.add_argument("port", nargs="?", type=int, default=8000, help="Port to listen on (default: 8000)")
    parser.add_argument("-d", "--directory", default=os.getcwd(), help="Directory to serve (default: current dir)")
    parser.add_argument("-b", "--bind", default="0.0.0.0", help="Bind address (default: 0.0.0.0)")
    parser.add_argument("-a", "--auth", default=None, help="Optional Basic Auth credentials in USER:PASS format")
    args = parser.parse_args()

    SERVER_ROOT = os.path.abspath(os.path.expanduser(args.directory))
    os.chdir(SERVER_ROOT)

    if args.auth:
        SERVER_AUTH_TOKEN = base64.b64encode(args.auth.encode("utf-8")).decode("ascii")

    lan_ip = get_lan_ip()
    with ThreadingHTTPServer((args.bind, args.port), TermuxHTTPRequestHandler) as httpd:
        print(f"\033[1;32m● Termux HTTP Server running\033[0m")
        print(f"  \033[1;36mDirectory:\033[0m {SERVER_ROOT}")
        print(f"  \033[1;36mLocal:\033[0m     http://127.0.0.1:{args.port}/")
        print(f"  \033[1;36mNetwork:\033[0m   http://{lan_ip}:{args.port}/")
        if SERVER_AUTH_TOKEN:
            print(f"  \033[1;33mAuth:\033[0m      Basic Auth enabled")
        print(f"  \033[0;90mPress Ctrl+C to stop\033[0m")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\n\033[1;33m● Server stopped.\033[0m")


if __name__ == "__main__":
    main()
Hide comments
