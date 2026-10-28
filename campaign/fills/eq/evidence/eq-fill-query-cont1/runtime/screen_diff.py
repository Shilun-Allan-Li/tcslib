"""New pairs of the after screen against the before screen. Usage: screen_diff.py <before> <after>"""
import re
import sys
def pairs(p):
    out = {}
    for l in open(p):
        m = re.match(r"^\s+(\S+)\s+reproduces\s+(\S+): (\d+)/(\d+) = (\d+)%", l)
        if m:
            out[(m.group(1), m.group(2))] = (int(m.group(3)), int(m.group(4)), int(m.group(5)))
    return out
b, a = pairs(sys.argv[1]), pairs(sys.argv[2])
own = "NTimeDiagonalizer.lean"
new = [(k, v) for k, v in a.items() if k not in b]
gone = [(k, v) for k, v in b.items() if k not in a]
print(f"before {len(b)} pairs; after {len(a)} pairs; new {len(new)}; gone {len(gone)}")
for (t, s), (x, y, pct) in sorted(new, key=lambda kv: -kv[1][2]):
    kind = "in-file" if own in t and own in s else ("cross-file (owned side)" if own in t or own in s else "other")
    print(f"NEW [{kind}] {t}  reproduces  {s}: {x}/{y} = {pct}%")
for (t, s), (x, y, pct) in gone:
    print(f"GONE {t}  reproduces  {s}: {x}/{y} = {pct}%")
