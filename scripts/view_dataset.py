"""
Flip through the theorem dataset in the terminal.

    python3 scripts/view_dataset.py                       # browse dataset/tcslib_theorems.jsonl
    python3 scripts/view_dataset.py path/to/other.jsonl
    python3 scripts/view_dataset.py --filter switching     # only ids containing "switching"
    python3 scripts/view_dataset.py --index 42             # start on entry 42
    python3 scripts/view_dataset.py --print 42             # just print entry 42 and exit (no TUI)

Keys:
    →  l  n  space     next entry          ←  h  p           previous entry
    ↓  j               scroll down         ↑  k              scroll up
    PgDn ^D            page down           PgUp ^U           page up
    g                  go to entry number  /                 search id substring (n/N to repeat)
    home 0             jump to top         q  esc            quit
"""

import argparse
import curses
import json
import textwrap
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
DEFAULT = BASE / "dataset" / "tcslib_theorems.jsonl"


def load(path: Path, filt: str | None):
    recs = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            r = json.loads(line)
            if filt and filt.lower() not in r.get("id", "").lower():
                continue
            recs.append(r)
    return recs


def entry_lines(rec):
    """Return [(text, style)] for one record. style in {head, meta, sec, code, ''}."""
    out = [(rec.get("id", "<no id>"), "head")]
    meta = f"{rec.get('kind','?')}  ·  {rec.get('source_module','?')}  ·  {rec.get('n_upstream_defs','?')} upstream defs"
    if rec.get("title"):
        meta += f"  ·  “{rec['title']}”"
    out.append((meta, "meta"))
    out.append(("", ""))
    out.append(("── INFORMAL ──────────────────────────────────", "sec"))
    for ln in (rec.get("informal_statement") or "").splitlines() or [""]:
        out.append((ln, ""))
    out.append(("", ""))
    ndefs = rec.get("n_upstream_defs")
    label = "── FORMAL" + (f"  ({ndefs} upstream defs) " if ndefs is not None else " ")
    out.append((label + "─" * max(0, 46 - len(label)), "sec"))
    for ln in (rec.get("formal_statement") or "").splitlines():
        out.append((ln, "code"))
    return out


def wrap_lines(lines, width):
    """Wrap (text, style) logical lines to display width, preserving blanks."""
    wrapped = []
    for text, style in lines:
        if text == "":
            wrapped.append(("", style))
            continue
        for piece in textwrap.wrap(text, width, drop_whitespace=False,
                                   replace_whitespace=False, subsequent_indent="    ") or [""]:
            wrapped.append((piece, style))
    return wrapped


def prompt(stdscr, msg):
    h, w = stdscr.getmaxyx()
    stdscr.move(h - 1, 0)
    stdscr.clrtoeol()
    stdscr.addstr(h - 1, 0, msg[: w - 1], curses.A_REVERSE)
    curses.echo()
    curses.curs_set(1)
    try:
        s = stdscr.getstr(h - 1, min(len(msg) + 1, w - 1), 64).decode("utf-8", "ignore")
    except Exception:
        s = ""
    curses.noecho()
    curses.curs_set(0)
    return s.strip()


def run(stdscr, recs, start_idx=0):
    curses.curs_set(0)
    styles = {}
    if curses.has_colors():
        curses.start_color()
        curses.use_default_colors()
        curses.init_pair(1, curses.COLOR_CYAN, -1)
        curses.init_pair(2, curses.COLOR_GREEN, -1)
        curses.init_pair(3, curses.COLOR_YELLOW, -1)
        curses.init_pair(4, curses.COLOR_WHITE, -1)
        styles = {
            "head": curses.color_pair(1) | curses.A_BOLD,
            "meta": curses.color_pair(2),
            "sec": curses.color_pair(3) | curses.A_BOLD,
            "code": curses.color_pair(4),
            "": curses.A_NORMAL,
        }
    else:
        styles = {"head": curses.A_BOLD, "meta": curses.A_NORMAL, "sec": curses.A_BOLD,
                  "code": curses.A_NORMAL, "": curses.A_NORMAL}

    idx = max(0, min(len(recs) - 1, start_idx))
    top = 0
    last_search = ""
    status = ""

    while True:
        h, w = stdscr.getmaxyx()
        body_h = max(1, h - 2)
        lines = wrap_lines(entry_lines(recs[idx]), w - 1)
        max_top = max(0, len(lines) - body_h)
        top = max(0, min(top, max_top))

        stdscr.erase()
        # header bar
        hdr = f" [{idx + 1}/{len(recs)}] "
        stdscr.addstr(0, 0, (hdr + " " * (w - len(hdr)))[: w - 1], curses.A_REVERSE)
        # body
        for row in range(body_h):
            li = top + row
            if li >= len(lines):
                break
            text, style = lines[li]
            try:
                stdscr.addstr(row + 1, 0, text[: w - 1], styles.get(style, curses.A_NORMAL))
            except curses.error:
                pass
        # footer
        more = "" if max_top == 0 else f"  ▲▼ {int(100 * top / max_top) if max_top else 0}%"
        foot = status or "n/p next/prev · j/k scroll · g goto · / search · q quit"
        stdscr.addstr(h - 1, 0, (foot + more + " " * w)[: w - 1], curses.A_REVERSE)
        stdscr.refresh()
        status = ""

        c = stdscr.getch()
        if c in (ord("q"), 27):  # q / esc
            break
        elif c in (ord("n"), ord("l"), ord(" "), curses.KEY_RIGHT):
            if idx < len(recs) - 1:
                idx += 1; top = 0
        elif c in (ord("p"), ord("h"), curses.KEY_LEFT):
            if idx > 0:
                idx -= 1; top = 0
        elif c in (ord("j"), curses.KEY_DOWN):
            top += 1
        elif c in (ord("k"), curses.KEY_UP):
            top -= 1
        elif c in (curses.KEY_NPAGE, 4):  # PgDn / ^D
            top += body_h - 1
        elif c in (curses.KEY_PPAGE, 21):  # PgUp / ^U
            top -= body_h - 1
        elif c in (ord("0"), curses.KEY_HOME):
            top = 0
        elif c == curses.KEY_END:
            top = max_top
        elif c == ord("g"):
            s = prompt(stdscr, "Go to entry #: ")
            if s.isdigit():
                idx = max(0, min(len(recs) - 1, int(s) - 1)); top = 0
        elif c in (ord("/"), ord("N")):
            if c == ord("/"):
                last_search = prompt(stdscr, "Search id: ") or last_search
            if last_search:
                found = next((j for j in range(idx + 1, len(recs)) if last_search.lower() in recs[j]["id"].lower()), None)
                if found is None:  # wrap around
                    found = next((j for j in range(0, idx + 1) if last_search.lower() in recs[j]["id"].lower()), None)
                if found is not None:
                    idx = found; top = 0
                    status = f"→ {recs[idx]['id']}"
                else:
                    status = f"no match for '{last_search}'"


def print_entry(rec):
    print(f"id: {rec.get('id')}")
    print(f"module: {rec.get('source_module')}  kind: {rec.get('kind')}  "
          f"upstream_defs: {rec.get('n_upstream_defs')}")
    print("\n── INFORMAL ──\n" + (rec.get("informal_statement") or ""))
    print("\n── FORMAL ──\n" + (rec.get("formal_statement") or ""))


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("path", nargs="?", default=str(DEFAULT))
    ap.add_argument("--filter", help="Only entries whose id contains this substring.")
    ap.add_argument("--index", type=int, default=1, help="1-based entry to start on.")
    ap.add_argument("--print", type=int, metavar="N", help="Print entry N and exit (no TUI).")
    args = ap.parse_args()

    path = Path(args.path)
    if not path.exists():
        print(f"Dataset not found: {path}\nBuild it with: python3 scripts/build_dataset.py")
        return 1
    recs = load(path, args.filter)
    if not recs:
        print("No entries to show" + (f" (filter={args.filter!r})" if args.filter else "") + ".")
        return 1

    if args.print is not None:
        if 1 <= args.print <= len(recs):
            print_entry(recs[args.print - 1])
            return 0
        print(f"Index out of range 1..{len(recs)}.")
        return 1

    start = max(1, min(len(recs), args.index))
    try:
        curses.wrapper(run, recs, start - 1)
    except curses.error as e:
        print(f"Could not start the TUI ({e}). Use --print N to view an entry instead.")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
