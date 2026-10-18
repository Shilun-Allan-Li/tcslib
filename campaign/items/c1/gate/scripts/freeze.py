"""Freeze check for a comment-only patch (read-only; standard library only).

Usage: python3 -I freeze.py <before.lean> <after.lean>

Strips every comment (block comments, docstrings and module docstrings `/- … -/`, nested, and
line comments `-- …`) from both files and compares what remains, line by line after removing
trailing whitespace and blank lines. Exit status 0 iff the code is identical; it also prints
the number of changed lines in the raw files and the declaration count of each side.
"""
import difflib
import re
import sys


def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if src.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(src[i])
        i += 1
    lines = [l.split("--")[0].rstrip() for l in "".join(out).splitlines()]
    return [l for l in lines if l.strip()]


a_raw = open(sys.argv[1], encoding="utf-8").read()
b_raw = open(sys.argv[2], encoding="utf-8").read()
a, b = strip(a_raw), strip(b_raw)
decl = re.compile(r"^\s*(?:theorem|lemma|def|structure|abbrev|inductive|instance)\b")
raw_changed = sum(1 for l in difflib.unified_diff(a_raw.splitlines(), b_raw.splitlines(), n=0)
                  if l[:1] in "+-" and not l.startswith(("+++", "---")))
print(f"raw lines changed (+/-): {raw_changed}")
print(f"code lines after stripping comments: before {len(a)}, after {len(b)}")
print(f"declarations: before {sum(bool(decl.match(l)) for l in a)}, "
      f"after {sum(bool(decl.match(l)) for l in b)}")
d = list(difflib.unified_diff(a, b, lineterm="", n=1))
if d:
    print("CODE DIFFERS:")
    print("\n".join(d))
    sys.exit(1)
print("FREEZE OK: comment-stripped code identical (no statement, proof or import changed)")
