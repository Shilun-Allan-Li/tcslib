"""List the backticked tokens that look like declaration names (read-only).

Usage: python3 -I cited.py <file> [<file> ...]   (a `.patch` file contributes its added lines)
Prints each distinct token once, sorted.
"""
import re, sys
toks = set()
for p in sys.argv[1:]:
    src = open(p, encoding="utf-8").read()
    if p.endswith(".patch"):
        src = "\n".join(l[1:] for l in src.split("\n") if l.startswith("+") and not l.startswith("+++"))
    for t in re.findall(r"`([^`\n]+)`", src):
        t = t.strip()
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.?!₀-₉]*", t) and not t.endswith(".lean"):
            if "." in t or t[0].isupper() or "_" in t:
                toks.add(t)
for t in sorted(toks):
    print(t)
