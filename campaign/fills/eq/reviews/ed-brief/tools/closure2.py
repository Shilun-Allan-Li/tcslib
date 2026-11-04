"""Forward closure of a start module, with one module's text replaced by an overlay file.
usage: python3 -I closure2.py <worktree> <overlay-file> <overlaid-module> <start-module>"""
import os, re, sys
wt, overlay, target, start = sys.argv[1:5]
def strip_comments(s):
    s = re.sub(r'/-.*?-/', '', s, flags=re.S)
    return re.sub(r'--[^\n]*', '', s)
def imps(m):
    if m == target: txt = open(overlay, encoding='utf-8').read()
    else:
        p = os.path.join(wt, *m.split('.')) + '.lean'
        txt = open(p, encoding='utf-8').read() if os.path.exists(p) else ''
    return [mm.group(1) for mm in re.finditer(r'^\s*import\s+(\S+)', strip_comments(txt), re.M)]
seen, order = set(), []
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in imps(m):
        if d.startswith('TCSlib'): visit(d)
    order.append(m)
visit(start)
ml = sorted({d for m in order for d in imps(m) if d.startswith('Mathlib')})
print('CLOSURE', len(order))
for m in order: print('  F', m.replace('.', '/'))
print('MATHLIB', len(ml))
for d in ml: print('  M', d)
