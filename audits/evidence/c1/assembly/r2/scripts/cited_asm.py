"""Cited-name population of a Lean file (read-only; standard library only).

Usage: python3 -I cited_asm.py <file.lean> <out.lean> [<extra import> ...]

Population (exactly): every backticked token inside the file's comments (block comments,
docstrings and module docstrings, nested, and line comments; found lexically, so code is never
scanned) that is a syntactically plain identifier: letters, digits, `_`, `'`, `.`, `!`, `?` and
subscript digits, starting with a letter or `_`, not ending in `.lean`. No other filter.
Writes <out.lean>: the file itself, the extra imports added after its imports, then
`open Turing Turing.NDTM Turing.MultiTapeTM Turing.FinTM Turing.FinNDTM` and one `#check @t`
per token; the unresolved tokens are the `unknown` errors of its elaboration. Prints the count.
"""
import re
import sys

src_path, out_path, extra = sys.argv[1], sys.argv[2], sys.argv[3:]
src = open(src_path, encoding="utf-8").read()


def comments(s):
    out, i, depth, cur = [], 0, 0, []
    while i < len(s):
        if s.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if s.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            if depth == 0:
                out.append("".join(cur))
                cur = []
            continue
        if depth > 0:
            cur.append(s[i])
            i += 1
            continue
        if s.startswith("--", i):
            j = s.find("\n", i)
            j = len(s) if j < 0 else j
            out.append(s[i + 2:j])
            i = j
            continue
        i += 1
    return out


toks = set()
for c in comments(src):
    for t in re.findall(r"`([^`\n]+)`", c):
        t = t.strip()
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.?!₀-₉]*", t) and not t.endswith(".lean"):
            toks.add(t)
lines = src.split("\n")
k = max(i for i, l in enumerate(lines) if l.startswith("import "))
lines[k + 1:k + 1] = [f"import {m}" for m in extra]
body = "\n".join(lines)
body += "\nopen Turing Turing.NDTM Turing.MultiTapeTM Turing.FinTM Turing.FinNDTM\n"
body += "".join(f"#check @{t}\n" for t in sorted(toks))
open(out_path, "w", encoding="utf-8").write(body)
print(len(toks))
