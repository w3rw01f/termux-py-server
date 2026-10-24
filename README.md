# Termux HTTP File Server

A lightweight, zero-dependency Python HTTP file server for Termux. The server,
HTML, CSS, and JavaScript are contained in `server.py`.

## Run

```sh
python server.py [port] [-d DIRECTORY] [-b BIND] [-a USER:PASS]
```

The defaults are port `8000`, the current directory, and bind address `0.0.0.0`.
For local development, use a disposable directory and bind to loopback:

```sh
python3 server.py 8000 -b 127.0.0.1 -d /path/to/scratch
```

Use `-a user:pass` to enable HTTP Basic Authentication. Share only intended files
and use a trusted network; Basic Authentication does not encrypt HTTP traffic.

## Features

- Dark interface with breadcrumbs, filtering, sorting, and optional dotfile display.
- Select mode with copy, move, rename, edit, and delete.
- Cross-folder clipboard with individual success, failure, and skipped results.
  Failed or skipped clipboard items remain available to retry after a refresh.
- Drag-and-drop or multi-file uploads with progress and cancellation. Existing
  names prompt for **Keep both**, **Skip**, or **Replace**; keep-both is the default.
  The selected policy is checked again when files are published. Uploads that did
  not need a prompt also use keep-both if a collision appears later.
- UTF-8 text viewer opens existing files in read mode. **Edit** reveals Save;
  Select → Edit and newly created files with “Open in editor” enabled enter edit
  mode directly. A non-selectable line-number gutter follows vertical scrolling,
  and long lines scroll horizontally without wrapping. Cursor and selection
  indicators, Tab indentation, Ctrl/Cmd+S, raw Open, and download remain available.
- Image, audio, and video previews with Prev / Open / Next controls and an icon
  download button. Media edges use narrow 11% tap zones; horizontal single-finger
  swipes navigate while pinch and vertical gestures are ignored. Fullscreen has
  synchronized expand/compress icons, the F shortcut, and a viewport fallback
  when the browser restricts the native API.
- Storage usage meter and an on-demand **Size** button in each directory row.
  Click again to recalculate. Sizes include hidden files and sum logical file
  lengths recursively, rather than allocated disk space. Links are skipped;
  `≈` marks results with skipped links, special files, or unreadable entries.

## File safety and limits

Uploads are streamed into private temporary files in the target directory. No
files are published until the entire multipart request is complete. Interrupted
or malformed uploads discard staged files; publication failures are reported per
file. Cancellation cannot undo files already published when the request finished.
Insufficient storage returns a clear error. Stalled connections time out after
30 seconds. Temporary files use the reserved `.termux-tmp-` prefix and are hidden
from listings and blocked from HTTP/API access. A process kill or power loss may
leave temporary files for manual cleanup after stopping the server.

Editor saves use a version token and atomic replacement. Conflicting saves are
rejected with HTTP `409`, leaving browser edits intact. Copy those edits before
reopening the current file to resolve the conflict. Binary files, invalid UTF-8,
and files larger than 2 MiB are rejected by the editor. Uniform CRLF/CR line
endings and file permissions are preserved. Atomic replacement changes the file's
inode; other hard links continue to reference the previous contents.

Symlinks can be listed, renamed, copied as links, moved, or deleted, but cannot be
opened or traversed. Filesystem operations
assume other local programs are trusted; path checks do not provide isolation
against a hostile process changing directories concurrently.

JSON requests are limited to 16 MiB; uploads accept up to 10,000 files per request.
Limits are constants near the top of `server.py`.

Single byte ranges, including suffix ranges, are supported. Multiple ranges and
unknown range units receive the full file. Batch operations continue after item
errors; a failed directory copy or move may have made partial filesystem changes.

## Tests

```sh
python3 -B -m unittest discover -s tests -v
```

Tests use the standard library, in-memory HTTP connections, and disposable files.
If Node.js is available, the same command also checks generated JavaScript syntax
and exercises editor modes and line numbers, swipe/pinch handling, fullscreen,
directory sizes, uploads, and clipboard behavior in a mock DOM. Node.js is optional and is not a server dependency.
