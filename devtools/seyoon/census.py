"""Text-scan sorry census, before/after, over a module list.
usage: python3 -I census.py <modules.txt> <before-root> <after-root>
Counts comment-stripped `sorry` tokens per file and names the declaration enclosing each
(the nearest preceding declaration header in the comment-stripped text). A missing file
counts as absent (0).
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leanlib import strip_keep_lines, decls

mods, broot, aroot = sys.argv[1:4]
TOK = re.compile(r'(?<![A-Za-z0-9_.\'])sorry(?![A-Za-z0-9_\'])')
def scan(path):
    if not os.path.exists(path): return None, []
    s = strip_keep_lines(open(path, encoding='utf-8').read())
    ds = decls(s); lines = s.split('\n'); hits = []
    for ln, l in enumerate(lines, 1):
        for _ in TOK.finditer(l):
            owner = None
            for d in ds:
                if d['line'] <= ln: owner = d
                else: break
            hits.append((ln, owner['name'] if owner else '?'))
    return len(hits), hits
tb = ta = 0; changed = []
print('module | before | after | sorried declarations after')
for m in [l.strip() for l in open(mods) if l.strip()]:
    f = m + '.lean'
    nb, hb = scan(os.path.join(broot, f)); na, ha = scan(os.path.join(aroot, f))
    tb += nb or 0; ta += na or 0
    names = sorted({h[1] for h in ha})
    print(f"{f} | {'absent' if nb is None else nb} | {na} | {', '.join(names)}")
    if (nb or 0) != (na or 0): changed.append((f, nb, na, sorted({h[1] for h in hb}), names))
print(f'TOTAL sorry tokens: before {tb}, after {ta}')
print('files whose count changed:')
for f, nb, na, b, a in changed:
    print(f'  {f}: {nb} -> {na}; before: {b}; after: {a}')
