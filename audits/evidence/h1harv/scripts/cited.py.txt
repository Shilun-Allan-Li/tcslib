"""List the backticked tokens of a Lean file's comments that look like declaration names."""
import re, sys
src = open(sys.argv[1], encoding="utf-8").read()
toks = set()
for t in re.findall(r"`([^`\n]+)`", src):
    t = t.strip()
    if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.?!₀-₉]*", t) and not t.endswith(".lean"):
        if "." in t or t[0].isupper() or "_" in t:
            toks.add(t)
for t in sorted(toks):
    print(t)
