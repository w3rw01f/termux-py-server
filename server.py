#!/usr/bin/env python3
"""
server.py — Lightweight, zero-dependency HTTP file server for Termux.
Features:
  - Termux-inspired dark minimalist UI with monospace typography
  - Sticky breadcrumb navigation bar at the top
  - Hamburger menu: Select mode, + Upload Files, + New Folder, + New Text File, Show .dotfiles (OFF by default)
  - Hidden-by-default checkboxes; Select mode reveals checkboxes & action bar (Copy, Move, Rename, Edit, Delete)
  - Persistent cross-folder clipboard bar (Copy/Cut items, navigate via breadcrumbs, Paste Here)
  - Top monochrome upload progress bar + drag-and-drop uploads + streamed multipart disk writes
  - Bottom storage usage bar showing free space / total space and color-coded fill meter
  - Read-first text viewer with synchronized line-number gutter, direct Edit mode, Open/download, cursor/selection indicators, Tab, and Ctrl+S
  - Media viewer with Prev / Open / Next, download, dynamic fullscreen icons, 11% edge taps, and pinch-aware swipe navigation
  - Optional HTTP Basic Authentication (-a / --auth user:pass)

Usage in Termux:
  python server.py [port] [-d DIRECTORY] [-b BIND] [-a USER:PASS]
"""

import argparse
import base64
import datetime
import hmac
import hashlib
import errno
import html
import io
import json
import os
import posixpath
import re
import shutil
import socket
import sys
import stat
import threading
import tempfile
import urllib.parse
from email.parser import BytesHeaderParser, HeaderParser
from contextlib import nullcontext
from http import HTTPStatus
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer

SERVER_ROOT = os.path.realpath(os.getcwd())
SERVER_AUTH_TOKEN = None  # Base64 "user:pass" when --auth is enabled

# Serialize mutations from this server; external filesystem writers remain independent.
FILE_LOCK = threading.RLock()
TEMP_PREFIX = ".termux-tmp-"
MAX_TEXT_BYTES = 2 * 1024 * 1024
MAX_JSON_BYTES = 16 * 1024 * 1024
MAX_UPLOAD_FILES = 10000


class RequestError(ValueError):
    def __init__(self, message, status=HTTPStatus.BAD_REQUEST):
        super().__init__(message)
        self.status = status


TEXT_EXTENSIONS = {
    ".txt", ".md", ".log", ".rst", ".csv", ".tsv", ".py", ".sh", ".bash", ".zsh",
    ".js", ".mjs", ".ts", ".tsx", ".jsx", ".json", ".html", ".htm", ".css", ".scss",
    ".c", ".h", ".cpp", ".hpp", ".rs", ".go", ".java", ".kt", ".kts", ".xml",
    ".yaml", ".yml", ".toml", ".ini", ".conf", ".cfg", ".sql", ".lua", ".rb",
    ".php", ".vim", ".env", ".gitignore", ".bashrc", ".zshrc", ".properties",
}

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
    if is_link:
        return ("LINK", "ft-link")
    if is_dir:
        return ("DIR", "ft-dir")
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


def human_size(num_bytes: int) -> str:
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if num_bytes < 1024 or unit == "TB":
            return f"{num_bytes:.0f} B" if unit == "B" else f"{num_bytes:.1f} {unit}"
        num_bytes /= 1024.0
    return f"{num_bytes:.1f} TB"


def resolve_safe_path(rel_url_path: str, allow_leaf_link=False) -> str:
    """Reject traversal and symlinks; leaf links may only be manipulated as links."""
    if not isinstance(rel_url_path, str) or "\0" in rel_url_path:
        raise ValueError("Invalid path")
    root = os.path.realpath(SERVER_ROOT)
    # API paths are decoded strings. HTTP paths are decoded once in translate_path.
    target = os.path.abspath(os.path.join(root, rel_url_path.lstrip("/")))
    if os.path.commonpath([root, target]) != root:
        raise ValueError("Path escapes root directory")
    current = root
    parts = os.path.relpath(target, root).split(os.sep)
    for index, part in enumerate(parts):
        if part.startswith(TEMP_PREFIX):
            raise ValueError("Temporary files are private")
        current = os.path.join(current, part)
        if os.path.islink(current) and not (allow_leaf_link and index == len(parts) - 1):
            raise ValueError("Opening or traversing symbolic links is disabled")
    return target


def validate_name(name: str, error: str) -> str:
    """Validate an already-trimmed file or folder name."""
    if (not name or "/" in name or "\\" in name or name in (".", "..")
            or name.startswith(TEMP_PREFIX) or any(ord(c) < 32 or ord(c) == 127 for c in name)):
        raise ValueError(error)
    return name


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


def read_text_version(target):
    with open(target, "rb") as source:
        raw = source.read(MAX_TEXT_BYTES + 1)
        metadata = os.fstat(source.fileno())
    if len(raw) > MAX_TEXT_BYTES:
        raise ValueError("File is larger than 2 MB; download to edit locally")
    if b"\0" in raw:
        raise ValueError("Binary files cannot be edited; download instead")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        raise ValueError("File is not valid UTF-8; download to edit without data loss") from None
    stamp = f"{metadata.st_mtime_ns}:{metadata.st_size}:{metadata.st_ino}".encode()
    version = hashlib.sha256(stamp + raw).hexdigest()
    return text, version, metadata


def save_text(target, content, version):
    if not isinstance(content, str) or "\0" in content or len(content.encode("utf-8")) > MAX_TEXT_BYTES:
        raise ValueError("Text must be a string of at most 2 MB")
    with FILE_LOCK:
        original, current_version, metadata = read_text_version(target)
        if version != current_version:
            raise RequestError("File changed since it was opened. Reopen it before saving; your edits are still in the editor.", HTTPStatus.CONFLICT)
        # Textareas normalize line endings. Preserve uniform CRLF/CR files on save.
        if "\r\n" in original and "\n" not in original.replace("\r\n", ""):
            content = content.replace("\r\n", "\n").replace("\n", "\r\n")
        elif "\r" in original and "\n" not in original:
            content = content.replace("\r\n", "\n").replace("\n", "\r")
        payload = content.encode("utf-8")
        if len(payload) > MAX_TEXT_BYTES:
            raise ValueError("Text exceeds 2 MB after preserving line endings")
        temp_path = None
        try:
            with tempfile.NamedTemporaryFile(dir=os.path.dirname(target), prefix=TEMP_PREFIX, delete=False) as temp:
                temp_path = temp.name
                temp.write(payload)
                temp.flush()
                os.fsync(temp.fileno())
                os.chmod(temp.name, stat.S_IMODE(metadata.st_mode))
            # Detect edits made outside this server while writing the temporary file.
            if read_text_version(target)[1] != current_version:
                raise RequestError("File changed while saving; reopen it before saving again", HTTPStatus.CONFLICT)
            os.replace(temp_path, target)
            return read_text_version(target)[1]
        finally:
            if temp_path and os.path.exists(temp_path):
                os.unlink(temp_path)


class MultipartReader:
    """Bounded streaming parser that retains boundaries split across reads."""
    def __init__(self, stream, length, boundary):
        self.stream, self.remaining = stream, length
        self.buffer = b""
        self.boundary = boundary

    def fill(self):
        if not self.remaining:
            raise ValueError("Upload ended before its closing boundary")
        chunk = self.stream.read(min(65536, self.remaining))
        if not chunk:
            raise ValueError("Upload was interrupted; incomplete files were discarded")
        self.remaining -= len(chunk)
        self.buffer += chunk

    def take_until(self, marker, limit):
        while marker not in self.buffer:
            if len(self.buffer) > limit:
                raise ValueError("Multipart headers are too large")
            self.fill()
        head, self.buffer = self.buffer.split(marker, 1)
        if len(head) > limit:
            raise ValueError("Multipart headers are too large")
        return head

    def body(self, output):
        marker = b"\r\n--" + self.boundary
        while True:
            index = self.buffer.find(marker)
            if index >= 0:
                while len(self.buffer) < index + len(marker) + 2:
                    self.fill()
                suffix = self.buffer[index + len(marker):index + len(marker) + 2]
                if suffix == b"--":
                    end = index + len(marker) + 2
                    while len(self.buffer) < end + 2 and self.remaining:
                        self.fill()
                    if self.buffer[end:end + 2] not in (b"", b"\r\n"):
                        suffix = b"invalid"
                if suffix in (b"--", b"\r\n"):
                    output.write(self.buffer[:index])
                    self.buffer = self.buffer[index + len(marker) + 2:]
                    return suffix == b"--"
                # A boundary-like string in binary data is ordinary payload.
                output.write(self.buffer[:index + 2])
                self.buffer = self.buffer[index + 2:]
            else:
                keep = len(marker) + 2
                if len(self.buffer) > keep:
                    output.write(self.buffer[:-keep])
                    self.buffer = self.buffer[-keep:]
                self.fill()


class TermuxHTTPRequestHandler(SimpleHTTPRequestHandler):
    server_version = "TermuxHTTP/3.3"

    def setup(self):
        self.request.settimeout(30)
        super().setup()

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

    def translate_path(self, path):
        decoded = urllib.parse.unquote(urllib.parse.urlsplit(path).path)
        return resolve_safe_path(decoded)

    def send_head(self):
        try:
            path = self.translate_path(self.path)
            if os.path.isdir(path):
                for index in ("index.html", "index.htm"):
                    if os.path.lexists(os.path.join(path, index)):
                        resolve_safe_path(os.path.relpath(os.path.join(path, index), SERVER_ROOT))
            if os.path.exists(path) and not (os.path.isdir(path) or os.path.isfile(path)):
                raise ValueError("Only regular files and directories can be opened")
            return super().send_head()
        except (ValueError, OSError) as exc:
            self.send_error(HTTPStatus.FORBIDDEN, str(exc))
            return None

    def do_HEAD(self):
        if self.check_auth():
            super().do_HEAD()

    def do_GET(self):
        if not self.check_auth():
            return
        try:
            path = self.translate_path(self.path)
            range_header = self.headers.get("Range")
            # Multiple/unknown range units are deliberately ignored (full 200).
            if range_header and "," not in range_header and range_header.startswith("bytes=") and os.path.isfile(path):
                if_range = self.headers.get("If-Range")
                if not if_range or if_range == self.date_time_string(os.path.getmtime(path)):
                    self.send_range_response(path, range_header)
                    return
        except (ValueError, OSError) as exc:
            self.send_error(HTTPStatus.FORBIDDEN, str(exc))
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

    def handle_file_upload(self, content_type: str):
        """Stage the entire multipart request before publishing completed files."""
        staged = []
        try:
            path = self.translate_path(self.path)
            if not os.path.isdir(path):
                raise ValueError("Target path is not a directory")
            policy = self.headers.get("X-Upload-Conflict", "keep")
            if policy not in ("keep", "skip", "replace"):
                raise ValueError("Invalid upload collision policy")
            message = BytesHeaderParser().parsebytes(("Content-Type: " + content_type + "\r\n\r\n").encode())
            boundary = message.get_boundary()
            if not boundary or len(boundary) > 200 or any(ord(c) < 32 or ord(c) > 126 for c in boundary):
                raise ValueError("Invalid multipart boundary")
            length = int(self.headers.get("Content-Length", "0"))
            if length <= 0:
                raise ValueError("Content-Length is required")
            if length > shutil.disk_usage(path).free:
                raise RequestError("Not enough free storage for this upload", HTTPStatus.INSUFFICIENT_STORAGE)
            reader = MultipartReader(self.rfile, length, boundary.encode("ascii"))
            if reader.take_until(b"\r\n", 204) != b"--" + boundary.encode("ascii"):
                raise ValueError("Invalid initial multipart boundary")
            while True:
                if len(staged) >= MAX_UPLOAD_FILES:
                    raise ValueError("Too many uploaded files")
                headers = HeaderParser().parsestr(reader.take_until(b"\r\n\r\n", 65536).decode("utf-8") + "\r\n\r\n")
                filename = headers.get_filename()
                if not filename:
                    raise ValueError("Every upload part must contain a filename")
                validate_name(filename, "Invalid upload filename")
                # Reject link destinations even for replacement; no content operation follows links.
                resolve_safe_path(os.path.relpath(os.path.join(path, filename), SERVER_ROOT))
                with tempfile.NamedTemporaryFile(dir=path, prefix=TEMP_PREFIX, delete=False) as output:
                    staged.append((filename, output.name))
                    final = reader.body(output)
                    output.flush()
                    os.fsync(output.fileno())
                if final:
                    break
            # Consume/check the remainder so a truncated request never publishes files.
            while reader.remaining:
                reader.fill()
                if len(reader.buffer) > 65536:
                    raise ValueError("Unexpected data after upload boundary")
            if reader.buffer not in (b"", b"\r\n"):
                raise ValueError("Unexpected data after upload boundary")
            results = []
            with FILE_LOCK:
                for filename, temp in staged:
                    result = {"path": filename}
                    try:
                        target = resolve_safe_path(os.path.relpath(os.path.join(path, filename), SERVER_ROOT))
                        if os.path.lexists(target):
                            if policy == "skip":
                                result.update(status="skipped", error="Already exists")
                                results.append(result)
                                continue
                            if policy == "keep":
                                target = unique_dest_path(path, filename)
                            elif not os.path.isfile(target):
                                raise ValueError("Cannot replace a directory or special file")
                        os.replace(temp, target)
                        result.update(status="success", name=os.path.basename(target))
                    except (OSError, ValueError) as exc:
                        result.update(status="failed", error=str(exc))
                    results.append(result)
            self.send_json(HTTPStatus.OK, {"ok": True, "results": results})
        except (OSError, ValueError) as exc:
            self.close_connection = True
            status = HTTPStatus.INSUFFICIENT_STORAGE if isinstance(exc, OSError) and exc.errno == errno.ENOSPC else getattr(exc, "status", HTTPStatus.BAD_REQUEST)
            try:
                self.send_json(status, {"ok": False, "error": str(exc)})
            except (BrokenPipeError, ConnectionResetError):
                pass
        finally:
            for _, temp in staged:
                if os.path.exists(temp):
                    os.unlink(temp)

    def handle_batch(self, data):
        action, items = data["action"], data.get("items")
        if not isinstance(items, list) or not items or not all(isinstance(p, str) for p in items):
            raise ValueError("Select one or more item paths")
        results = []
        with FILE_LOCK:
            for rel in items:
                result = {"path": rel}
                try:
                    source = resolve_safe_path(rel, allow_leaf_link=True)
                    if source == os.path.realpath(SERVER_ROOT):
                        raise ValueError("Cannot modify the server root directory")
                    if not os.path.lexists(source):
                        result.update(status="skipped", error="Item no longer exists")
                    elif action == "delete":
                        if os.path.islink(source) or not os.path.isdir(source):
                            os.unlink(source)
                        else:
                            shutil.rmtree(source)
                        result["status"] = "success"
                    else:
                        dest = resolve_safe_path(data.get("dest_dir", "/"))
                        if not os.path.isdir(dest):
                            raise ValueError("Destination directory does not exist")
                        name = os.path.basename(source)
                        target = os.path.join(dest, name)
                        if not os.path.islink(source) and os.path.isdir(source) and os.path.commonpath([source, dest]) == source:
                            raise ValueError("Cannot copy or move a folder into itself")
                        if action == "copy":
                            target = unique_dest_path(dest, name)
                            if os.path.isdir(source) and not os.path.islink(source):
                                shutil.copytree(source, target, symlinks=True)
                            else:
                                shutil.copy2(source, target, follow_symlinks=False)
                        elif source == target:
                            result.update(status="skipped", error="Already in the destination directory")
                        elif os.path.lexists(target):
                            raise ValueError("An item with this name already exists in the destination")
                        else:
                            shutil.move(source, target)
                        result.setdefault("status", "success")
                except (ValueError, OSError) as exc:
                    result.update(status="failed", error=str(exc))
                results.append(result)
        succeeded = sum(r["status"] == "success" for r in results)
        return {"ok": True, "results": results, "deleted" if action == "delete" else "processed": succeeded}

    def handle_api_action(self):
        """Handle JSON file operations: delete, rename, copy, move, mkdir, touch, read_text, write_text, upload_conflicts, directory_size."""
        try:
            content_length = int(self.headers.get("Content-Length", 0))
            if not 0 < content_length <= MAX_JSON_BYTES:
                raise ValueError("JSON request must be between 1 byte and 16 MB")
            raw = self.rfile.read(content_length)
            if len(raw) != content_length:
                raise ValueError("Incomplete JSON request")
            data = json.loads(raw)
            if not isinstance(data, dict):
                raise ValueError("JSON request must be an object")
        except Exception as exc:
            self.close_connection = True
            self.send_json(HTTPStatus.BAD_REQUEST, {"ok": False, "error": f"Invalid JSON: {exc}"})
            return

        action = data.get("action")
        try:
            with FILE_LOCK if action in ("delete", "copy", "move", "rename", "mkdir", "touch", "write_text") else nullcontext():
                if action in ("delete", "copy", "move"):
                    self.send_json(HTTPStatus.OK, self.handle_batch(data))

                elif action == "rename":
                    src_rel = data.get("src", "")
                    new_name = (data.get("new_name") or "").strip()
                    if not src_rel or not new_name:
                        raise ValueError("Source and new name are required")
                    validate_name(new_name, "Invalid file or folder name")
                    src_path = resolve_safe_path(src_rel, allow_leaf_link=True)
                    if src_path == os.path.realpath(SERVER_ROOT):
                        raise ValueError("Cannot rename server root")
                    dest_path = os.path.join(os.path.dirname(src_path), new_name)
                    if os.path.exists(dest_path) or os.path.islink(dest_path):
                        raise ValueError(f"'{new_name}' already exists")
                    os.rename(src_path, dest_path)
                    self.send_json(HTTPStatus.OK, {"ok": True})

                elif action == "mkdir":
                    dir_rel = data.get("dir", "/")
                    folder_name = validate_name((data.get("name") or "").strip(), "Invalid folder name")
                    parent_dir = resolve_safe_path(dir_rel)
                    new_dir = os.path.join(parent_dir, folder_name)
                    if os.path.exists(new_dir):
                        raise ValueError(f"'{folder_name}' already exists")
                    os.makedirs(new_dir)
                    self.send_json(HTTPStatus.OK, {"ok": True})

                elif action == "touch":
                    dir_rel = data.get("dir", "/")
                    file_name = validate_name((data.get("name") or "").strip(), "Invalid file name")
                    if "." not in file_name:
                        file_name += ".txt"
                    parent_dir = resolve_safe_path(dir_rel)
                    new_file = os.path.join(parent_dir, file_name)
                    if os.path.exists(new_file) or os.path.islink(new_file):
                        raise ValueError(f"'{file_name}' already exists")
                    with open(new_file, "x", encoding="utf-8") as f:
                        f.write("")
                    rel_created = posixpath.join(dir_rel, file_name)
                    self.send_json(HTTPStatus.OK, {"ok": True, "path": rel_created, "name": file_name})

                elif action == "read_text":
                    rel_path = data.get("path", "")
                    target = resolve_safe_path(rel_path)
                    if not os.path.isfile(target):
                        raise ValueError("File does not exist")
                    content, version, _ = read_text_version(target)
                    self.send_json(HTTPStatus.OK, {"ok": True, "path": rel_path, "name": os.path.basename(target), "content": content, "version": version})

                elif action == "write_text":
                    target = resolve_safe_path(data.get("path", ""))
                    if not os.path.isfile(target):
                        raise ValueError("File does not exist")
                    version = save_text(target, data.get("content", ""), data.get("version"))
                    self.send_json(HTTPStatus.OK, {"ok": True, "version": version})

                elif action == "upload_conflicts":
                    parent = resolve_safe_path(data.get("dir", "/"))
                    names = data.get("names", [])
                    if not isinstance(names, list) or not all(isinstance(name, str) for name in names):
                        raise ValueError("Upload names must be a list of strings")
                    conflicts = [name for name in names if os.path.lexists(os.path.join(parent, validate_name(name, "Invalid filename")))]
                    self.send_json(HTTPStatus.OK, {"ok": True, "conflicts": conflicts})

                elif action == "directory_size":
                    target = resolve_safe_path(data.get("path", "/"))
                    if not os.path.isdir(target):
                        raise ValueError("Path is not a directory")
                    size = files = skipped = 0
                    stack = [target]
                    while stack:
                        directory = stack.pop()
                        try:
                            resolve_safe_path(os.path.relpath(directory, SERVER_ROOT))
                            with os.scandir(directory) as entries:
                                for entry in entries:
                                    if entry.name.startswith(TEMP_PREFIX) or entry.is_symlink():
                                        skipped += 1
                                        continue
                                    try:
                                        if entry.is_dir(follow_symlinks=False):
                                            stack.append(entry.path)
                                        elif entry.is_file(follow_symlinks=False):
                                            size += entry.stat(follow_symlinks=False).st_size
                                            files += 1
                                        else:
                                            skipped += 1
                                    except OSError:
                                        skipped += 1
                        except (OSError, ValueError):
                            skipped += 1
                    self.send_json(HTTPStatus.OK, {"ok": True, "bytes": size, "files": files, "skipped": skipped})

                else:
                    self.send_json(HTTPStatus.BAD_REQUEST, {"ok": False, "error": f"Unknown action: {action}"})
        except Exception as exc:
            self.send_json(getattr(exc, "status", HTTPStatus.BAD_REQUEST), {"ok": False, "error": str(exc)})

    def send_range_response(self, path: str, range_header: str):
        try:
            file_size = os.path.getsize(path)
            match = re.fullmatch(r"bytes=([0-9]{0,20})-([0-9]{0,20})", range_header)
            start = end = 0
            valid = bool(match and any(match.groups()) and file_size)
            if valid:
                first, last = match.groups()
                if first:
                    start = int(first)
                    end = min(int(last), file_size - 1) if last else file_size - 1
                    valid = start < file_size and start <= end
                else:
                    suffix = int(last)
                    valid = suffix > 0
                    start, end = max(0, file_size - suffix), file_size - 1
            if not valid:
                self.send_response(HTTPStatus.REQUESTED_RANGE_NOT_SATISFIABLE)
                self.send_header("Content-Range", f"bytes */{file_size}")
                self.send_header("Content-Length", "0")
                self.end_headers()
                return

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
            entries = [name for name in os.listdir(path) if not name.startswith(TEMP_PREFIX)]
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
            is_link = os.path.islink(full_path)
            is_dir = not is_link and os.path.isdir(full_path)
            try:
                st = os.lstat(full_path)
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
            editable = int(not is_link and is_text_editable(name, is_dir))
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
                "is_link": int(is_link),
                "editable": editable,
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
            size_html = (
                f'<button type="button" class="btn dir-size-btn" aria-label="Calculate size of {esc_raw_name}" title="Calculate directory size; symbolic links are skipped">Size</button>'
                if it["is_dir"] else it["size_str"]
            )
            rows_html.append(
                f'<tr class="item-row"{hidden_attr} '
                f'data-isdir="{it["is_dir"]}" '
                f'data-islink="{it["is_link"]}" '
                f'data-editable="{it["editable"]}" '
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
                f'<td class="col-size">{size_html}</td>'
                f'<td class="col-date">{it["mtime_str"]}</td>'
                f"</tr>"
            )

        rows_str = "\n".join(rows_html)
        enc = sys.getfilesystemencoding()
        title = html.escape(url_path)
        current_dir_js = json.dumps(url_path).replace("<", "\\u003c")

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
    --warn: #fb923c;
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
  .stats-bar, .footer-bar {{
    display: flex;
    justify-content: space-between;
    align-items: center;
    flex-wrap: wrap;
    gap: 10px;
    color: var(--muted);
    font-size: 12px;
    padding: 0 4px;
  }}
  .stats-bar {{ margin-bottom: 8px; }}
  .operation-status {{ margin-left: auto; max-width: 100%; min-width: 0; }}
  .status-message {{
    background: none;
    border: none;
    color: inherit;
    font: inherit;
    text-align: left;
    cursor: pointer;
    text-decoration: underline dotted;
    text-underline-offset: 3px;
  }}
  .operation-status .status-message {{
    max-width: 40ch;
    min-width: 0;
    overflow: hidden;
    text-overflow: ellipsis;
    white-space: nowrap;
  }}
  .status-message[data-level="success"] {{ color: var(--accent); }}
  .status-message[data-level="warning"] {{ color: var(--warn); }}
  .status-message[data-level="error"] {{ color: var(--danger); }}
  #operationBackdrop {{ z-index: 120; }}
  .editor-modal.operation-modal {{ height: auto; max-height: 80vh; max-width: 760px; }}
  #operationBackdrop .editor-header {{ flex-shrink: 0; }}
  .operation-details {{
    margin: 0;
    padding: 16px;
    overflow: auto;
    white-space: pre-wrap;
    overflow-wrap: anywhere;
    font: inherit;
    font-size: 13px;
    min-height: 80px;
  }}
  /* Storage Footer Bar below File List */
  .footer-bar {{ margin-top: 10px; }}
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
  .fill-warn {{ background: var(--warn); }}
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
  .dir-size-btn {{ font-size: 11px; padding: 3px 7px; }}
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
  .modal, .editor-modal, .lightbox-modal {{
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 10px;
    width: 100%;
  }}
  .editor-modal, .lightbox-modal {{
    max-width: 960px;
    display: flex;
    flex-direction: column;
    overflow: hidden;
  }}
  .modal {{
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
    height: min(86vh, 760px);
    box-shadow: 0 18px 48px rgba(0, 0, 0, 0.8);
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
  .editor-body {{
    flex: 1;
    min-height: 0;
    display: flex;
    overflow: hidden;
    background: #090b0f;
    position: relative;
  }}
  .editor-gutter {{
    background: #0b0e14;
    color: var(--muted);
    border-right: 1px solid var(--border);
    padding: 14px 10px 14px 12px;
    font-family: inherit;
    font-size: 13.5px;
    line-height: 1.55;
    text-align: right;
    user-select: none;
    overflow: hidden;
    min-width: 48px;
    white-space: pre;
    flex-shrink: 0;
  }}
  .editor-textarea {{
    flex: 1;
    min-width: 0;
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
    white-space: pre;
    overflow-wrap: normal;
    overflow-x: auto;
    overflow-y: auto;
  }}
  .editor-textarea[readonly] {{
    background: #0b0d12;
    color: var(--file);
    cursor: default;
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
    max-height: 90vh;
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
    touch-action: pan-y pinch-zoom;
  }}
  .lightbox-modal.is-fullscreen {{ position: fixed; inset: 0; }}
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
  /* Narrow edge taps leave the center and bottom media controls accessible. */
  .edge-tap-zone {{
    position: absolute;
    top: 0;
    bottom: 56px;
    width: 11%;
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
    padding-left: 10px;
    background: linear-gradient(90deg, rgba(0, 0, 0, 0.35), transparent);
  }}
  .edge-tap-zone.edge-right {{
    right: 0;
    justify-content: flex-end;
    padding-right: 10px;
    background: linear-gradient(270deg, rgba(0, 0, 0, 0.35), transparent);
  }}
  .edge-tap-zone:hover,
  .edge-tap-zone:active {{
    opacity: 1;
  }}
  .edge-chevron {{
    color: rgba(226, 232, 240, 0.75);
    font-size: 18px;
    font-weight: 700;
    background: rgba(19, 23, 32, 0.72);
    border: 1px solid var(--border);
    border-radius: 999px;
    width: 30px;
    height: 30px;
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
    <div id="uploadBar" class="storage-info operation-status" role="status" aria-live="polite" style="display:none">
      <div id="uploadMeter" class="storage-meter" style="display:none">
        <div id="uploadFill" class="storage-fill fill-neutral" style="width: 0%"></div>
      </div>
      <button type="button" id="uploadText" class="status-message" aria-haspopup="dialog" aria-controls="operationBackdrop" title="View operation details"></button>
      <button type="button" id="cancelUploadBtn" class="btn btn-danger" style="display:none">Cancel upload</button>
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

<!-- Details are opened on demand; operation results never block the next action. -->
<div id="operationBackdrop" class="modal-backdrop">
  <section class="editor-modal operation-modal" role="dialog" aria-modal="true" aria-labelledby="operationTitle">
    <div class="editor-header">
      <span id="operationTitle" class="editor-title">Operation details</span>
      <button type="button" id="operationCloseBtn" class="btn">Close</button>
    </div>
    <pre id="operationDetails" class="operation-details" tabindex="0"></pre>
  </section>
</div>

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
    <label id="uploadPolicyRow" style="display:none">
      Existing files
      <select id="uploadPolicy" class="modal-input">
        <option value="keep">Keep both</option>
        <option value="skip">Skip existing files</option>
        <option value="replace">Replace existing files</option>
      </select>
    </label>
    <button type="button" id="modalStatus" class="status-message" aria-haspopup="dialog" aria-controls="operationBackdrop" style="display:none"></button>
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
        <button type="button" id="editorEditBtn" class="btn btn-primary">Edit</button>
        <button type="button" id="editorSaveBtn" class="btn btn-primary" style="display:none">Save</button>
        <button type="button" id="editorCloseBtn" class="btn">Close</button>
      </div>
    </div>
    <div class="editor-body">
      <div id="editorGutter" class="editor-gutter" aria-hidden="true">1</div>
      <textarea id="editorTextarea" class="editor-textarea" aria-label="File contents" spellcheck="false" wrap="off" readonly></textarea>
    </div>
    <div class="editor-footer">
      <div class="editor-footer-left">
        <span id="editorCursorPos" class="cursor-pos">Ln 1, Col 1</span>
        <span id="editorStats">0 lines, 0 chars</span>
      </div>
      <button type="button" id="editorStatus" class="status-message" aria-haspopup="dialog" aria-controls="operationBackdrop" title="View latest operation details">Read-only mode</button>
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
        <button type="button" id="lightboxFullscreenBtn" class="btn btn-icon" title="Enter fullscreen" aria-label="Enter fullscreen" aria-pressed="false">
          <svg id="fsIconExpand" aria-hidden="true" viewBox="0 0 24 24"><polyline points="15 3 21 3 21 9"/><polyline points="9 21 3 21 3 15"/><line x1="21" y1="3" x2="14" y2="10"/><line x1="3" y1="21" x2="10" y2="14"/></svg>
          <svg id="fsIconCompress" aria-hidden="true" viewBox="0 0 24 24" style="display:none"><polyline points="4 14 10 14 10 20"/><polyline points="20 10 14 10 14 4"/><line x1="14" y1="10" x2="21" y2="3"/><line x1="3" y1="21" x2="10" y2="14"/></svg>
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

  const byId = id => document.getElementById(id);
  const filterInput = byId('filterInput');
  const hamburgerBtn = byId('hamburgerBtn');
  const dropdownMenu = byId('dropdownMenu');
  const menuSelectBtn = byId('menuSelectBtn');
  const selectStateBadge = byId('selectStateBadge');
  const menuUploadBtn = byId('menuUploadBtn');
  const menuNewFolderBtn = byId('menuNewFolderBtn');
  const menuNewTxtBtn = byId('menuNewTxtBtn');
  const fileUpload = byId('fileUpload');
  const toggleDotBtn = byId('toggleDotBtn');
  const dotStateBadge = byId('dotStateBadge');

  const uploadBar = byId('uploadBar');
  const uploadFill = byId('uploadFill');
  const uploadMeter = byId('uploadMeter');
  const uploadText = byId('uploadText');
  const cancelUploadBtn = byId('cancelUploadBtn');
  let activeUpload = null;
  let uploadProgressText = '';
  let uploadFileDetails = '';
  let lastOperation = null;
  let statusPersisted = false;
  let statusReturnFocus = null;
  const OPERATION_STATUS_KEY = 'termux_http_operation_v1';
  const operationBackdrop = byId('operationBackdrop');
  const operationDetails = byId('operationDetails');
  const operationCloseBtn = byId('operationCloseBtn');
  const modalStatus = byId('modalStatus');

  const tbody = byId('fileBody');
  const rows = Array.from(tbody.querySelectorAll('.item-row'));
  const headers = Array.from(document.querySelectorAll('th[data-sort]'));
  const selectAllCheck = byId('selectAllCheck');

  const selectionBar = byId('selectionBar');
  const selectedCountText = byId('selectedCountText');
  const actCopyBtn = byId('actCopyBtn');
  const actMoveBtn = byId('actMoveBtn');
  const actRenameBtn = byId('actRenameBtn');
  const actEditBtn = byId('actEditBtn');
  const actDeleteBtn = byId('actDeleteBtn');
  const actExitSelectBtn = byId('actExitSelectBtn');

  const clipboardBar = byId('clipboardBar');
  const clipboardText = byId('clipboardText');
  const pasteHereBtn = byId('pasteHereBtn');
  const clearClipboardBtn = byId('clearClipboardBtn');

  const modalBackdrop = byId('modalBackdrop');
  const modalTitle = byId('modalTitle');
  const modalDesc = byId('modalDesc');
  const modalInput = byId('modalInput');
  const uploadPolicyRow = byId('uploadPolicyRow');
  const uploadPolicy = byId('uploadPolicy');
  const modalCheckRow = byId('modalCheckRow');
  const modalExtraCheck = byId('modalExtraCheck');
  const modalCheckLabel = byId('modalCheckLabel');
  const modalCancelBtn = byId('modalCancelBtn');
  const modalConfirmBtn = byId('modalConfirmBtn');

  const editorBackdrop = byId('editorBackdrop');
  const editorTitle = byId('editorTitle');
  const editorOpenLink = byId('editorOpenLink');
  const editorRawLink = byId('editorRawLink');
  const editorEditBtn = byId('editorEditBtn');
  const editorGutter = byId('editorGutter');
  const editorSaveBtn = byId('editorSaveBtn');
  const editorCloseBtn = byId('editorCloseBtn');
  const editorTextarea = byId('editorTextarea');
  const editorCursorPos = byId('editorCursorPos');
  const editorStats = byId('editorStats');
  const editorStatus = byId('editorStatus');

  const lightboxBackdrop = byId('lightboxBackdrop');
  const lightboxModal = byId('lightboxModal');
  const lightboxBody = byId('lightboxBody');
  const fsIconExpand = byId('fsIconExpand');
  const fsIconCompress = byId('fsIconCompress');
  const lightboxTitle = byId('lightboxTitle');
  const lightboxMediaSlot = byId('lightboxMediaSlot');
  const edgeTapLeft = byId('edgeTapLeft');
  const edgeTapRight = byId('edgeTapRight');
  const lightboxPrevBtn = byId('lightboxPrevBtn');
  const lightboxOpenLink = byId('lightboxOpenLink');
  const lightboxNextBtn = byId('lightboxNextBtn');
  const lightboxDownloadLink = byId('lightboxDownloadLink');
  const lightboxFullscreenBtn = byId('lightboxFullscreenBtn');
  const lightboxCloseBtn = byId('lightboxCloseBtn');

  // .dotfiles OFF by default
  let showDotfiles = localStorage.getItem(DOTFILES_KEY) === '1';
  let selectMode = false;
  let sortKey = 'name';
  let sortAsc = true;
  let modalHandler = null;

  let currentEditorPath = null;
  let currentEditorVersion = null;
  let editorIsEditing = false;
  let lastGutterLineCount = 0;
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
  async function uploadFileList(files) {{
    if (!files || !files.length) return;
    if (activeUpload) {{ showStatus('Upload in progress', 'An upload is already in progress. Wait for it to finish or cancel it.'); return; }}
    files = Array.from(files);
    try {{
      const data = await apiCall({{ action: 'upload_conflicts', dir: CURRENT_DIR, names: files.map(f => f.name) }});
      if (data.conflicts.length) {{
        openModal({{
          title: 'Files already exist',
          desc: `Choose how to handle existing files: ${{data.conflicts.join(', ')}}`,
          showInput: false,
          showUploadPolicy: true,
          confirmLabel: 'Upload',
          onConfirm: () => {{ startUpload(files, uploadPolicy.value); return false; }},
        }});
      }} else {{
        startUpload(files, 'keep');
      }}
    }} catch (err) {{ showStatus('Upload failed', err.message, 'error'); }}
  }}

  function startUpload(files, policy) {{
    if (activeUpload) return;
    const formData = new FormData();
    files.forEach(f => formData.append('file', f));
    const xhr = activeUpload = new XMLHttpRequest();
    uploadFill.style.width = '0%';
    uploadProgressText = 'Uploading...';
    uploadFileDetails = files.map(f => f.name).join('\\n');
    renderOperationStatus();
    cancelUploadBtn.disabled = false;
    xhr.upload.addEventListener('progress', (e) => {{
      if (!e.lengthComputable) return;
      const pct = Math.min(100, Math.round((e.loaded / e.total) * 100));
      uploadFill.style.width = `${{pct}}%`;
      uploadProgressText = pct === 100 ? 'Finishing upload...' : `${{formatBytes(e.loaded)}} / ${{formatBytes(e.total)}} (${{pct}}%)`;
      renderOperationStatus();
    }});
    xhr.addEventListener('load', () => {{
      activeUpload = null;
      cancelUploadBtn.disabled = true;
      try {{
        const data = JSON.parse(xhr.responseText);
        if (xhr.status < 200 || xhr.status >= 300 || !data.ok) throw new Error(data.error || 'Upload failed');
        showResults(data, 'Upload');
        reloadAfterOperation();
      }} catch (err) {{
        showStatus('Upload failed', err.message, 'error');
      }}
    }});
    xhr.addEventListener('error', () => {{
      activeUpload = null;
      cancelUploadBtn.disabled = true;
      showStatus('Upload connection lost', 'Refresh to check completed files before retrying.\\n' + uploadFileDetails, 'error');
    }});
    xhr.addEventListener('abort', () => {{
      activeUpload = null;
      cancelUploadBtn.disabled = true;
      showStatus('Upload cancelled', 'Refresh to check whether the upload had already completed.\\n' + uploadFileDetails, 'warning');
    }});
    xhr.open('POST', window.location.pathname);
    xhr.setRequestHeader('X-Upload-Conflict', policy);
    xhr.send(formData);
  }}

  cancelUploadBtn.addEventListener('click', () => {{ if (activeUpload) activeUpload.abort(); }});

  menuUploadBtn.addEventListener('click', () => {{
    dropdownMenu.classList.remove('open');
    fileUpload.click();
  }});
  fileUpload.addEventListener('change', () => {{
    if (fileUpload.files.length > 0) uploadFileList(fileUpload.files);
    fileUpload.value = '';
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
    actDeleteBtn.disabled = count === 0;
    actRenameBtn.disabled = count !== 1;
    actEditBtn.disabled = !(count === 1 && selected[0].dataset.isdir === '0' && selected[0].dataset.islink !== '1');
    selectAllCheck.checked = visible.length > 0 && visible.every(r => r.querySelector('.row-check').checked);
    selectAllCheck.indeterminate = count > 0 && !selectAllCheck.checked;
  }}

  rows.forEach(r => {{
    const cb = r.querySelector('.row-check');
    const link = r.querySelector('.row-link');
    cb.addEventListener('change', updateSelectionUI);
    const sizeButton = r.querySelector('.dir-size-btn');
    if (sizeButton) sizeButton.addEventListener('click', async (e) => {{
      e.stopPropagation();
      sizeButton.disabled = true;
      sizeButton.textContent = '...';
      try {{
        const data = await apiCall({{ action: 'directory_size', path: r.dataset.path }});
        sizeButton.textContent = `${{data.skipped ? '≈ ' : ''}}${{formatBytes(data.bytes)}}`;
        sizeButton.title = `${{data.files}} files; ${{data.skipped}} links or unreadable entries skipped. Click to recalculate.`;
        sizeButton.setAttribute('aria-label', `${{r.dataset.rawname}}: ${{sizeButton.textContent}}. Click to recalculate.`);
        r.dataset.size = String(data.bytes);
        showStatus('Directory size ready', `${{r.dataset.rawname}}: ${{formatBytes(data.bytes)}}\\n${{data.files}} files; ${{data.skipped}} links or unreadable entries skipped.`, data.skipped ? 'warning' : 'success');
      }} catch (err) {{
        sizeButton.textContent = 'Retry';
        sizeButton.title = err.message;
        showStatus('Size calculation failed', err.message, 'error');
      }} finally {{ sizeButton.disabled = false; }}
    }});
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

  function queueSelected(mode) {{
    const paths = getSelectedRows().map(r => r.dataset.path);
    if (!paths.length) return;
    setClipboard(mode, paths);
    setSelectMode(false);
  }}

  actCopyBtn.addEventListener('click', () => queueSelected('copy'));
  actMoveBtn.addEventListener('click', () => queueSelected('move'));

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

  function renderOperationStatus() {{
    uploadBar.style.display = activeUpload || lastOperation ? 'inline-flex' : 'none';
    uploadMeter.style.display = activeUpload ? '' : 'none';
    cancelUploadBtn.style.display = activeUpload ? '' : 'none';
    uploadText.textContent = activeUpload ? uploadProgressText : lastOperation ? lastOperation.summary : '';
    uploadText.dataset.level = activeUpload ? 'info' : lastOperation ? lastOperation.level : 'info';
    uploadText.title = `${{uploadText.textContent}} — click for details`;
    if (operationBackdrop.classList.contains('open')) renderOperationDetails();
  }}

  function renderOperationDetails() {{
    const progress = activeUpload ? `${{uploadProgressText}}\\n${{uploadFileDetails}}\\n\\n` : '';
    operationDetails.textContent = progress + (lastOperation ? `${{lastOperation.summary}}\\n\\n${{lastOperation.details}}` : '');
  }}

  function showStatus(summary, details = summary, level = 'info') {{
    lastOperation = {{ summary, details, level }};
    statusPersisted = false;
    try {{
      sessionStorage.setItem(OPERATION_STATUS_KEY, JSON.stringify(lastOperation));
      statusPersisted = true;
    }} catch {{ /* Keep full details in memory if browser storage is unavailable. */ }}
    renderOperationStatus();
  }}

  function restoreOperationStatus() {{
    try {{
      const value = JSON.parse(sessionStorage.getItem(OPERATION_STATUS_KEY) || 'null');
      if (value && typeof value.summary === 'string' && typeof value.details === 'string' &&
          ['info', 'success', 'warning', 'error'].includes(value.level)) {{
        lastOperation = value;
        statusPersisted = true;
      }}
    }} catch {{ /* A missing or malformed saved message does not block the file list. */ }}
    renderOperationStatus();
  }}

  function reloadAfterOperation() {{
    if (statusPersisted) {{ window.location.reload(); return; }}
    if (lastOperation) {{
      lastOperation.details += '\\n\\nRefresh the page to update the file list after reviewing these details.';
      renderOperationStatus();
    }}
  }}

  function openOperationDetails() {{
    if (!lastOperation && !activeUpload) return;
    statusReturnFocus = document.activeElement;
    renderOperationDetails();
    operationBackdrop.classList.add('open');
    operationCloseBtn.focus();
  }}

  function closeOperationDetails() {{
    operationBackdrop.classList.remove('open');
    if (statusReturnFocus && statusReturnFocus.isConnected !== false) statusReturnFocus.focus();
  }}

  uploadText.addEventListener('click', openOperationDetails);
  editorStatus.addEventListener('click', openOperationDetails);
  modalStatus.addEventListener('click', openOperationDetails);
  operationCloseBtn.addEventListener('click', closeOperationDetails);
  operationBackdrop.addEventListener('click', e => {{
    if (e.target === operationBackdrop) closeOperationDetails();
  }});

  function showResults(data, label) {{
    const results = data.results || [];
    const count = status => results.filter(r => r.status === status).length;
    const succeeded = count('success'), failed = count('failed'), skipped = count('skipped');
    const summary = `${{label}}: ${{succeeded}} done${{failed ? `, ${{failed}} failed` : ''}}${{skipped ? `, ${{skipped}} skipped` : ''}}`;
    const details = results.map(r => `${{r.path}}: ${{r.status}}${{r.error ? ' — ' + r.error : r.name ? ' → ' + r.name : ''}}`);
    showStatus(summary, [`${{succeeded}} succeeded, ${{failed}} failed, ${{skipped}} skipped`, ...details].join('\\n'),
      failed ? 'error' : skipped ? 'warning' : 'success');
  }}

  pasteHereBtn.addEventListener('click', async () => {{
    const clip = getClipboard();
    if (!clip || !clip.items.length) return;
    pasteHereBtn.disabled = true;
    try {{
      const result = await apiCall({{
        action: clip.mode,
        items: clip.items,
        dest_dir: CURRENT_DIR,
      }});
      showResults(result, clip.mode === 'move' ? 'Move' : 'Copy');
      const pending = result.results.filter(r => r.status !== 'success').map(r => r.path);
      if (pending.length) setClipboard(clip.mode, pending);
      else clearClipboard();
      reloadAfterOperation();
    }} catch (err) {{
      showStatus('Transfer failed', err.message, 'error');
      pasteHereBtn.disabled = false;
    }}
  }});

  // Edit button in Select Bar
  actEditBtn.addEventListener('click', () => {{
    const sel = getSelectedRows();
    if (sel.length !== 1) return;
    const r = sel[0];
    setSelectMode(false);
    openEditor(r.dataset.path, r.dataset.rawname, r.dataset.href, false, true);
  }});

  // Inline Text Viewer / Editor functions
  function setEditorMode(editing) {{
    editorIsEditing = Boolean(editing);
    editorTextarea.readOnly = !editorIsEditing;
    editorEditBtn.style.display = editorIsEditing ? 'none' : 'inline-flex';
    editorSaveBtn.style.display = editorIsEditing ? 'inline-flex' : 'none';
    if (editorIsEditing) {{
      editorStatus.textContent = editorDirty ? 'Unsaved changes' : 'Editing — Ctrl+S to save';
      editorTextarea.focus();
    }} else {{
      editorStatus.textContent = 'Read-only mode';
    }}
  }}

  editorEditBtn.addEventListener('click', () => {{
    setEditorMode(true);
  }});

  function updateEditorGutter(lineCount) {{
    const count = Math.max(1, lineCount);
    if (count !== lastGutterLineCount) {{
      lastGutterLineCount = count;
      const nums = new Array(count);
      for (let i = 0; i < count; i++) nums[i] = i + 1;
      editorGutter.textContent = nums.join('\\n');
    }}
  }}

  function syncEditorGutter() {{
    // A horizontal scrollbar shortens the textarea viewport; match its scroll range.
    const scrollbar = Math.max(0, editorTextarea.offsetHeight - editorTextarea.clientHeight);
    editorGutter.style.paddingBottom = `${{14 + scrollbar}}px`;
    editorGutter.scrollTop = editorTextarea.scrollTop;
  }}

  editorTextarea.addEventListener('scroll', syncEditorGutter);
  window.addEventListener('resize', syncEditorGutter);

  function updateEditorStats() {{
    const val = editorTextarea.value;
    const lines = val ? val.split('\\n').length : 1;
    editorStats.textContent = `${{lines}} line${{lines === 1 ? '' : 's'}}, ${{val.length}} chars`;
    updateEditorGutter(lines);
    syncEditorGutter();
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

  async function openEditor(relPath, displayName, rawHref, reloadOnClose, startInEditMode = false) {{
    try {{
      const data = await apiCall({{ action: 'read_text', path: relPath }});
      currentEditorPath = relPath;
      currentEditorVersion = data.version;
      editorReloadOnClose = Boolean(reloadOnClose);
      editorDirty = false;
      lastGutterLineCount = 0;
      const targetHref = rawHref || encodeURIComponent(data.name);
      editorTitle.textContent = data.name || displayName;
      editorOpenLink.href = targetHref;
      editorRawLink.href = targetHref;
      editorTextarea.value = data.content || '';
      editorTextarea.scrollTop = editorTextarea.scrollLeft = editorGutter.scrollTop = 0;
      editorTextarea.setSelectionRange(0, 0);
      setEditorMode(startInEditMode);
      updateEditorStats();
      editorBackdrop.classList.add('open');
      setTimeout(() => {{
        if (startInEditMode) editorTextarea.focus();
        syncEditorGutter();
        updateEditorCursorPos();
      }}, 20);
    }} catch (err) {{
      showStatus('Could not open file', err.message, 'error');
    }}
  }}

  async function saveEditorContent() {{
    if (!currentEditorPath || !editorIsEditing || editorSaveBtn.disabled) return;
    const savedContent = editorTextarea.value;
    editorSaveBtn.disabled = true;
    editorStatus.textContent = 'Saving...';
    try {{
      const data = await apiCall({{
        action: 'write_text',
        path: currentEditorPath,
        content: savedContent,
        version: currentEditorVersion,
      }});
      currentEditorVersion = data.version;
      editorDirty = editorTextarea.value !== savedContent;
      editorReloadOnClose = true;
      editorTitle.textContent = editorTitle.textContent.replace(/\\*$/, '') + (editorDirty ? '*' : '');
      editorStatus.textContent = editorDirty ? 'Earlier changes saved; newer edits are unsaved' : 'Saved ✓';
      showStatus(editorDirty ? 'Saved; newer edits pending' : 'File saved', `${{currentEditorPath}}\\n${{editorStatus.textContent}}`, 'success');
    }} catch (err) {{
      showStatus('Save failed', `${{currentEditorPath}}\\n${{err.message}}`, 'error');
      editorStatus.textContent = 'Save failed';
    }} finally {{
      editorSaveBtn.disabled = false;
    }}
  }}

  function closeEditor() {{
    if (editorSaveBtn.disabled) {{ showStatus('Save in progress', 'Please wait for the save to finish'); return; }}
    if (editorDirty && !confirm('Discard unsaved changes?')) return;
    editorBackdrop.classList.remove('open');
    currentEditorPath = null;
    if (editorReloadOnClose) {{
      reloadAfterOperation();
    }}
  }}

  editorTextarea.addEventListener('input', () => {{
    if (!editorIsEditing) return;
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
    }} else if (editorIsEditing && e.key === 'Tab') {{
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
  function syncFullscreenIcon() {{
    const active = document.fullscreenElement === lightboxModal || lightboxModal.classList.contains('is-fullscreen');
    fsIconExpand.style.display = active ? 'none' : 'block';
    fsIconCompress.style.display = active ? 'block' : 'none';
    lightboxFullscreenBtn.setAttribute('aria-pressed', String(active));
    lightboxFullscreenBtn.setAttribute('aria-label', active ? 'Exit fullscreen' : 'Enter fullscreen');
    lightboxFullscreenBtn.title = active ? 'Exit fullscreen' : 'Enter fullscreen';
  }}

  document.addEventListener('fullscreenchange', syncFullscreenIcon);

  function openLightboxForRow(targetRow) {{
    lightboxItems = getVisibleRows().filter(r => Boolean(r.dataset.preview));
    lightboxIndex = lightboxItems.indexOf(targetRow);
    if (lightboxIndex === -1) return;
    resetSwipe();
    renderLightboxItem();
    syncFullscreenIcon();
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

    const tag = {{ image: 'img', video: 'video', audio: 'audio' }}[kind];
    if (!tag) return;
    const media = document.createElement(tag);
    media.src = href;
    if (kind === 'image') {{
      media.alt = name;
    }} else {{
      media.controls = true;
      media.autoplay = true;
    }}
    lightboxMediaSlot.appendChild(media);
  }}

  async function toggleLightboxFullscreen() {{
    if (document.fullscreenElement === lightboxModal) {{
      try {{ await document.exitFullscreen(); }} catch {{}}
    }} else if (lightboxModal.classList.contains('is-fullscreen')) {{
      lightboxModal.classList.remove('is-fullscreen');
    }} else {{
      try {{
        if (!lightboxModal.requestFullscreen) throw new Error('Fullscreen API unavailable');
        await lightboxModal.requestFullscreen();
      }} catch {{
        lightboxModal.classList.add('is-fullscreen');
      }}
    }}
    syncFullscreenIcon();
  }}

  async function closeLightbox() {{
    if (document.fullscreenElement === lightboxModal) {{
      try {{ await document.exitFullscreen(); }} catch {{}}
    }}
    lightboxModal.classList.remove('is-fullscreen');
    syncFullscreenIcon();
    resetSwipe();
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
    if (Date.now() >= suppressEdgeTapUntil) stepLightbox(-1);
  }});
  edgeTapRight.addEventListener('click', (e) => {{
    e.stopPropagation();
    if (Date.now() >= suppressEdgeTapUntil) stepLightbox(1);
  }});
  lightboxFullscreenBtn.addEventListener('click', toggleLightboxFullscreen);
  lightboxCloseBtn.addEventListener('click', closeLightbox);
  lightboxBackdrop.addEventListener('click', (e) => {{
    if (e.target === lightboxBackdrop) closeLightbox();
  }});

  // Swipe only once per single-finger gesture; pinch/vertical/control gestures pass through.
  let swipeStart = null;
  let multiTouchActive = false;
  let suppressEdgeTapUntil = 0;

  function resetSwipe() {{
    swipeStart = null;
    multiTouchActive = false;
  }}

  lightboxBody.addEventListener('touchstart', (e) => {{
    if (e.touches.length !== 1 || multiTouchActive) {{
      multiTouchActive = true;
      swipeStart = null;
      return;
    }}
    const touch = e.touches[0];
    const control = e.target && e.target.closest && e.target.closest('audio, video, button, a, input, select');
    if (control && (control.tagName !== 'VIDEO' || touch.clientY >= control.getBoundingClientRect().bottom - 56)) {{
      swipeStart = null;
      return;
    }}
    swipeStart = {{ id: touch.identifier, x: touch.clientX, y: touch.clientY }};
  }}, {{ passive: true }});

  lightboxBody.addEventListener('touchmove', (e) => {{
    if (e.touches.length > 1) {{ multiTouchActive = true; swipeStart = null; }}
  }}, {{ passive: true }});

  lightboxBody.addEventListener('touchend', (e) => {{
    const start = swipeStart;
    swipeStart = null;
    if (multiTouchActive) {{
      if (!e.touches.length) multiTouchActive = false;
      return;
    }}
    if (!start || e.touches.length) return;
    const end = Array.from(e.changedTouches || []).find(t => t.identifier === start.id);
    if (!end) return;
    const dx = end.clientX - start.x;
    const dy = end.clientY - start.y;
    if (Math.abs(dx) > 48 && Math.abs(dx) > Math.abs(dy) * 1.5) {{
      suppressEdgeTapUntil = Date.now() + 400;
      stepLightbox(dx < 0 ? 1 : -1);
    }}
  }}, {{ passive: true }});
  lightboxBody.addEventListener('touchcancel', resetSwipe, {{ passive: true }});

  // Modal helpers (Rename, New Folder, New Text File, Delete)
  function openModal({{
    title,
    desc,
    defaultValue = '',
    showInput = true,
    showCheckbox = false,
    showUploadPolicy = false,
    checkboxLabel = 'Open in editor after creation',
    checkboxDefault = true,
    danger = false,
    confirmLabel = 'Confirm',
    onConfirm,
  }}) {{
    modalStatus.style.display = 'none';
    modalTitle.textContent = title;
    modalDesc.textContent = desc;
    modalInput.style.display = showInput ? 'block' : 'none';
    modalInput.value = defaultValue;
    uploadPolicyRow.style.display = showUploadPolicy ? 'block' : 'none';
    uploadPolicy.value = 'keep';
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
        reloadAfterOperation();
      }}
    }} catch (err) {{
      showStatus(`${{modalTitle.textContent}} failed`, err.message, 'error');
      modalStatus.textContent = 'Operation failed — view details';
      modalStatus.dataset.level = 'error';
      modalStatus.style.display = 'block';
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
      confirmLabel: 'Rename',
      onConfirm: async (newName) => {{
        if (!newName || newName === oldName) return false;
        await apiCall({{ action: 'rename', src: srcPath, new_name: newName }});
        showStatus('Rename complete', `${{srcPath}} → ${{newName}}`, 'success');
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
        showResults(await apiCall({{ action: 'delete', items: sel.map(r => r.dataset.path) }}), 'Delete');
      }},
    }});
  }});

  // New Folder action inside hamburger menu
  menuNewFolderBtn.addEventListener('click', () => {{
    dropdownMenu.classList.remove('open');
    openModal({{
      title: 'New Folder',
      desc: `Create a folder inside ${{CURRENT_DIR}}:`,
      confirmLabel: 'Create',
      onConfirm: async (folderName) => {{
        if (!folderName) throw new Error('Folder name is required');
        await apiCall({{ action: 'mkdir', dir: CURRENT_DIR, name: folderName }});
        showStatus('Folder created', `${{CURRENT_DIR}}${{folderName}}`, 'success');
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
      showCheckbox: true,
      confirmLabel: 'Create',
      onConfirm: async (rawName, openAfter) => {{
        if (!rawName) throw new Error('File name is required');
        const res = await apiCall({{ action: 'touch', dir: CURRENT_DIR, name: rawName }});
        showStatus('File created', res.path, 'success');
        if (openAfter) {{
          await openEditor(res.path, res.name, encodeURIComponent(res.name), true, true);
          return false; // Wait until editor closes to reload list
        }}
        return true;
      }},
    }});
  }});

  // Keyboard shortcuts
  window.addEventListener('keydown', (e) => {{
    if (operationBackdrop.classList.contains('open')) {{
      if (e.key === 'Escape') {{ e.preventDefault(); closeOperationDetails(); }}
      else if (e.key === 'Tab') {{
        e.preventDefault();
        (document.activeElement === operationCloseBtn ? operationDetails : operationCloseBtn).focus();
      }}
      return;
    }}
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
  restoreOperationStatus();
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

    SERVER_ROOT = os.path.realpath(os.path.expanduser(args.directory))
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