"""
Wire newly-created chapter files into blueprint/src/chapter/main.tex.

Step 3 of the blueprint pipeline. After the `blueprint-writer` subagents have
created/extended `.tex` files, this scans the chapter tree for any file that is
not yet `\\input{...}`'d by main.tex and appends the missing ones, grouped by
area, under a marked block. Idempotent: running it twice is a no-op.

Usage:
    python3 scripts/blueprint_assemble.py            # apply
    python3 scripts/blueprint_assemble.py --check     # report only, exit 1 if missing
"""

import argparse
import re
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
CHAPTER_DIR = BASE / "blueprint" / "src" / "chapter"
MAIN_TEX = CHAPTER_DIR / "main.tex"
MARKER = "% --- auto-added by blueprint_assemble.py ---"

INPUT_RE = re.compile(r"\\input\{chapter/([^}]+)\}")


def existing_inputs(text: str) -> set[str]:
    return {m.group(1) for m in INPUT_RE.finditer(text)}


def all_chapter_files() -> list[str]:
    rels = []
    for tex in CHAPTER_DIR.rglob("*.tex"):
        rel = tex.relative_to(CHAPTER_DIR).as_posix()
        if rel == "main.tex":
            continue
        rels.append(rel)
    return sorted(rels)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true", help="Report missing inputs only; do not edit.")
    args = ap.parse_args()

    text = MAIN_TEX.read_text(encoding="utf-8") if MAIN_TEX.exists() else ""
    have = existing_inputs(text)
    missing = [rel for rel in all_chapter_files() if rel not in have]

    if not missing:
        print("main.tex is up to date — every chapter file is \\input.")
        return 0

    print(f"{len(missing)} chapter file(s) not yet in main.tex:")
    for rel in missing:
        print(f"  + {rel}")

    if args.check:
        return 1

    # Group missing by top-level area for tidy insertion.
    by_area: dict[str, list[str]] = {}
    for rel in missing:
        area = rel.split("/")[0] if "/" in rel else "(root)"
        by_area.setdefault(area, []).append(rel)

    block_lines = ["", MARKER]
    for area in sorted(by_area):
        block_lines.append(f"% {area}")
        for rel in sorted(by_area[area]):
            block_lines.append(f"\\input{{chapter/{rel}}}")
    block = "\n".join(block_lines) + "\n"

    new_text = text.rstrip("\n") + "\n" + block
    MAIN_TEX.write_text(new_text, encoding="utf-8")
    print(f"\nAppended {len(missing)} \\input line(s) to {MAIN_TEX.relative_to(BASE)}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
