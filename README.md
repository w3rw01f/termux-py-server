Lightweight, zero-dependency HTTP file server for Termux.
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
