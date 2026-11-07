"""sorrycensus.py <root>: per-file count of the `sorry` token outside comments and docstrings."""
import os, re, sys
root = sys.argv[1]; tot = 0; rows = []
for dp, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    for f in fs:
        if not f.endswith('.lean'): continue
        p = os.path.join(dp, f); src = open(p, encoding='utf-8').read()
        src = re.sub(r'/-.*?-/', '', src, flags=re.S); src = re.sub(r'--[^\n]*', '', src)
        n = len(re.findall(r'(?<![\w.])sorry(?![\w])', src))
        if n: rows.append((os.path.relpath(p, root), n)); tot += n
for r in sorted(rows): print(f"{r[1]:4d} {r[0]}")
print(f"TOTAL {tot}")
