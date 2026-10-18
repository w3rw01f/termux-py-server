#!/usr/bin/env python3
"""
termux_server.py — Lightweight, zero-dependency HTTP file server for Termux.
Features:
  - Termux-inspired dark minimalist UI with monospace typography
  - Sticky breadcrumb navigation bar at the top
  - Color-coded badges and filenames by filetype (Folders, Code, Media, Images, Archives, Docs)
  - Instant client-side search filter, column sorting, and drag-and-drop file upload
  - HTTP Range request support (206 Partial Content) for smooth video/audio streaming

Usage in Termux:
  python termux_server.py [port] [-d DIRECTORY]
"""

import argparse
import datetime
import html
import io
import mimetypes
import os
import posixpath
import re
import shutil
import socket
import sys
import urllib.parse
from http import HTTPStatus
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer

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
            ".zip", ".tar", ".gz", ".tgz", ".bz2", ".xz", ".txz", ".zst",
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


def human_size(num_bytes: int) -> str:
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if num_bytes < 1024 or unit == "TB":
            return f"{num_bytes:.0f} B" if unit == "B" else f"{num_bytes:.1f} {unit}"
        num_bytes /= 1024.0
    return f"{num_bytes:.1f} TB"


class TermuxHTTPRequestHandler(SimpleHTTPRequestHandler):
    server_version = "TermuxHTTP/1.0"

    def end_headers(self):
        self.send_header("Accept-Ranges", "bytes")
        super().end_headers()

    def do_GET(self):
        range_header = self.headers.get("Range")
        if range_header:
            path = self.translate_path(self.path)
            if os.path.isfile(path):
                self.send_range_response(path, range_header)
                return
        super().do_GET()

    def do_POST(self):
        """Handle simple multipart file uploads to the current directory."""
        path = self.translate_path(self.path)
        if not os.path.isdir(path):
            self.send_error(HTTPStatus.BAD_REQUEST, "Target path is not a directory")
            return

        content_type = self.headers.get("Content-Type", "")
        if "multipart/form-data" not in content_type:
            self.send_error(HTTPStatus.BAD_REQUEST, "Expected multipart/form-data")
            return

        boundary_match = re.search(r"boundary=([^;]+)", content_type)
        if not boundary_match:
            self.send_error(HTTPStatus.BAD_REQUEST, "Missing multipart boundary")
            return

        boundary = boundary_match.group(1).strip('"').encode("utf-8")
        content_length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(content_length)

        parts = body.split(b"--" + boundary)
        saved_count = 0
        for part in parts:
            if b"Content-Disposition" not in part:
                continue
            header_end = part.find(b"\r\n\r\n")
            if header_end == -1:
                continue
            raw_headers = part[:header_end].decode("utf-8", errors="replace")
            fn_match = re.search(r'filename="([^"]+)"', raw_headers)
            if not fn_match or not fn_match.group(1):
                continue
            filename = os.path.basename(fn_match.group(1))
            file_data = part[header_end + 4 :]
            if file_data.endswith(b"\r\n"):
                file_data = file_data[:-2]
            dest = os.path.join(path, filename)
            with open(dest, "wb") as f:
                f.write(file_data)
            saved_count += 1

        self.send_response(HTTPStatus.SEE_OTHER)
        self.send_header("Location", self.path)
        self.end_headers()

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
            display_name = name + "/" if is_dir else name
            href = urllib.parse.quote(name, errors="surrogatepass") + ("/" if is_dir else "")
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
                "is_dir": 1 if is_dir else 0,
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
                f'<td class="col-name"><a href="{parent_href}" class="row-link ft-dir">'
                f'<span class="badge badge-dir">UP</span><span class="fname">.. (Parent Directory)</span></a></td>'
                f'<td class="col-size">—</td>'
                f'<td class="col-date">—</td>'
                f"</tr>"
            )

        for it in items:
            hidden_attr = ' data-hidden="1"' if it["hidden"] else ""
            rows_html.append(
                f'<tr class="item-row"{hidden_attr} '
                f'data-isdir="{it["is_dir"]}" '
                f'data-name="{html.escape(it["name"].lower())}" '
                f'data-size="{it["size"]}" '
                f'data-mtime="{it["mtime"]:.0f}">'
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
    --border: #232b3a;
    --text: #e2e8f0;
    --muted: #64748b;
    --accent: #22c55e;
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
    padding-bottom: 48px;
  }}
  /* Sticky Top Breadcrumb + Toolbar */
  header {{
    position: sticky;
    top: 0;
    z-index: 20;
    background: rgba(12, 14, 18, 0.92);
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
    flex-wrap: wrap;
  }}
  .search-input {{
    background: var(--surface);
    color: var(--text);
    border: 1px solid var(--border);
    border-radius: 6px;
    padding: 5px 10px;
    font-family: inherit;
    font-size: 13px;
    width: 190px;
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
    padding: 5px 10px;
    font-family: inherit;
    font-size: 12px;
    cursor: pointer;
    transition: border-color 0.15s, background 0.15s;
  }}
  .btn:hover {{
    background: var(--surface-hover);
    border-color: var(--muted);
  }}
  .btn.active {{
    border-color: var(--accent);
    color: var(--accent);
  }}
  main {{
    max-width: 1100px;
    margin: 14px auto 0;
    padding: 0 16px;
  }}
  .stats-bar {{
    display: flex;
    justify-content: space-between;
    align-items: center;
    color: var(--muted);
    font-size: 12px;
    margin-bottom: 8px;
    padding: 0 4px;
  }}
  .table-wrap {{
    background: var(--surface);
    border: 1px solid var(--border);
    border-radius: 8px;
    overflow: hidden;
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
  th:hover {{
    color: var(--text);
  }}
  td {{
    border-bottom: 1px solid rgba(35, 43, 58, 0.55);
    padding: 0;
  }}
  tr:last-child td {{
    border-bottom: none;
  }}
  tr:hover td {{
    background: var(--surface-hover);
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

  .upload-form {{ display: inline-flex; align-items: center; gap: 6px; }}
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
      <input type="search" id="filterInput" class="search-input" placeholder="Filter files (/)..." autocomplete="off">
      <button type="button" id="toggleDotBtn" class="btn" title="Toggle dotfiles">.dotfiles</button>
      <form class="upload-form" method="POST" enctype="multipart/form-data">
        <label class="btn" for="fileUpload">+ Upload</label>
        <input type="file" id="fileUpload" name="file" multiple style="display:none" onchange="this.form.submit()">
      </form>
    </div>
  </div>
</header>

<main>
  <div class="stats-bar">
    <span>{dir_count} folders, {file_count} files</span>
    <span id="visibleCount"></span>
  </div>
  <div class="table-wrap">
    <table id="fileTable">
      <thead>
        <tr>
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
</main>

<script>
(() => {{
  const filterInput = document.getElementById('filterInput');
  const toggleDotBtn = document.getElementById('toggleDotBtn');
  const tbody = document.getElementById('fileBody');
  const rows = Array.from(tbody.querySelectorAll('.item-row'));
  const headers = Array.from(document.querySelectorAll('th[data-sort]'));
  let showDotfiles = false;
  let sortKey = 'name';
  let sortAsc = true;

  toggleDotBtn.classList.toggle('active', showDotfiles); applyFilter();

  function applyFilter() {{
    const q = filterInput.value.trim().toLowerCase();
    let shown = 0;
    for (const r of rows) {{
      const isHidden = r.dataset.hidden === '1';
      const name = r.dataset.name || '';
      const matchDot = showDotfiles || !isHidden;
      const matchQuery = !q || name.includes(q);
      const visible = matchDot && matchQuery;
      r.style.display = visible ? '' : 'none';
      if (visible) shown++;
    }}
  }}

  filterInput.addEventListener('input', applyFilter);
  toggleDotBtn.addEventListener('click', () => {{
    showDotfiles = !showDotfiles;
    toggleDotBtn.classList.toggle('active', showDotfiles);
    applyFilter();
  }});

  window.addEventListener('keydown', (e) => {{
    if (e.key === '/' && document.activeElement !== filterInput) {{
      e.preventDefault();
      filterInput.focus();
    }} else if (e.key === 'Escape' && document.activeElement === filterInput) {{
      filterInput.value = '';
      filterInput.blur();
      applyFilter();
    }}
  }});

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
    parser = argparse.ArgumentParser(description="Termux Dark Minimalist HTTP File Server")
    parser.add_argument("port", nargs="?", type=int, default=8000, help="Port to listen on (default: 8000)")
    parser.add_argument("-d", "--directory", default=os.getcwd(), help="Directory to serve (default: current dir)")
    parser.add_argument("-b", "--bind", default="0.0.0.0", help="Bind address (default: 0.0.0.0)")
    args = parser.parse_args()

    target_dir = os.path.abspath(os.path.expanduser(args.directory))
    os.chdir(target_dir)

    lan_ip = get_lan_ip()
    with ThreadingHTTPServer((args.bind, args.port), TermuxHTTPRequestHandler) as httpd:
        print(f"\033[1;32m● Termux HTTP Server running\033[0m")
        print(f"  \033[1;36mDirectory:\033[0m {target_dir}")
        print(f"  \033[1;36mLocal:\033[0m     http://127.0.0.1:{args.port}/")
        print(f"  \033[1;36mNetwork:\033[0m   http://{lan_ip}:{args.port}/")
        print(f"  \033[0;90mPress Ctrl+C to stop\033[0m")
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\n\033[1;33m● Server stopped.\033[0m")


if __name__ == "__main__":
    main()
