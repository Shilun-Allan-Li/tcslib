"""Independent import-closure derivation for the E-D review (reads files only).
usage: python3 -I closure.py <worktree> <overlay-file> <target-module>"""
import os, re, sys
wt, overlay, target = sys.argv[1:4]
IMP = re.compile(r'^\s*import\s+(\S+)', re.M)
def strip_comments(s):
    s = re.sub(r'/-.*?-/', '', s, flags=re.S)
    return re.sub(r'--[^\n]*', '', s)
def imports_of_text(s):
    head = strip_comments(s)
    out = []
    for line in head.split('\n'):
        m = re.match(r'^\s*import\s+(\S+)', line)
        if m: out.append(m.group(1))
        elif line.strip() and not line.strip().startswith('import') and out:
            # imports precede everything else; stop at first non-import, non-blank line
            if not line.strip().startswith('set_option') and not line.strip().startswith('/-'):
                pass
    return out
def mod_path(m):
    return os.path.join(wt, *m.split('.')) + '.lean'
cache = {}
def imps(m):
    if m in cache: return cache[m]
    if m == target:
        txt = open(overlay, encoding='utf-8').read()
    else:
        p = mod_path(m)
        txt = open(p, encoding='utf-8').read() if os.path.exists(p) else ''
    cache[m] = imports_of_text(txt)
    return cache[m]
# forward closure (TCSlib modules) and Mathlib roots
seen, order, stack = set(), [], []
def visit(m):
    if m in seen: return
    seen.add(m)
    for d in imps(m):
        if d.startswith('TCSlib'): visit(d)
    order.append(m)
visit(target)
tcs = [m for m in order]
mathlib = set()
for m in tcs:
    for d in imps(m):
        if d.startswith('Mathlib'): mathlib.add(d)
print('FORWARD_CLOSURE', len(tcs))
for m in tcs: print('  F', m)
print('MATHLIB_DIRECT_IMPORTS', len(mathlib))
for m in sorted(mathlib): print('  M', m)
# reverse dependents of target across the tree
allmods = []
for root, _, files in os.walk(os.path.join(wt, 'TCSlib')):
    for f in files:
        if f.endswith('.lean'):
            rel = os.path.relpath(os.path.join(root, f), wt)[:-5]
            allmods.append(rel.replace(os.sep, '.'))
if os.path.exists(os.path.join(wt, 'TCSlib.lean')): allmods.append('TCSlib')
rev = set([target]); changed = True
while changed:
    changed = False
    for m in allmods:
        if m not in rev and any(d in rev for d in imps(m)):
            rev.add(m); changed = True
print('REVERSE_DEPENDENTS', len(rev) - 1)
for m in sorted(rev - {target}): print('  R', m)
