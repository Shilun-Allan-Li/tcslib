"""Parse-only check of v3's scope tracking over every .lean file under <root>/TCSlib (and TCSlib.lean)."""
import os, sys
v3, root = sys.argv[1], sys.argv[2]
src = open(v3, encoding='utf-8').read()
head = src[:src.index('decls = []')]
sys.argv = [v3, root]
ns = {}; exec(compile(head, v3, 'exec'), ns)
files = ['TCSlib.lean'] if os.path.exists(os.path.join(root, 'TCSlib.lean')) else []
for d, _, fs in os.walk(os.path.join(root, 'TCSlib')):
    files += [os.path.relpath(os.path.join(d, f), root) for f in fs if f.endswith('.lean')]
n = 0; unclosed = 0
for p in sorted(files):
    t = ns['strip'](open(os.path.join(root, p), encoding='utf-8').read())
    ev = ns['scopes'](p, t); n += 1
    if ev[-1][1] != '': unclosed += 1; print(f"open namespace at EOF: {p}: {ev[-1][1]}")
print(f"files parsed: {n}; files ending inside a namespace: {unclosed}")
