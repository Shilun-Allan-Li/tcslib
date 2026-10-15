"""Inventory of the received files.
usage: python3 -I inventory.py <wt> <added.txt> <modified.txt> <before-dir>
Added files: path, lines, max line length (characters), public/private declaration counts
(comment-stripped), imports. Modified files: lines before/after, declaration counts before/after.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from leanlib import strip_keep_lines, decls, imports

wt, added, modified, before = sys.argv[1:5]
def info(path):
    src = open(path, encoding='utf-8').read()
    lines = src.split('\n')
    if lines and lines[-1] == '': lines = lines[:-1]
    ds = decls(strip_keep_lines(src))
    pub = sum(1 for d in ds if not d['private']); priv = len(ds) - pub
    kinds = {}
    for d in ds: kinds[d['kind']] = kinds.get(d['kind'], 0) + 1
    return len(lines), max((len(l) for l in lines), default=0), pub, priv, kinds, imports(src)

A = [l.strip() for l in open(added) if l.strip()]
M = [l.strip() for l in open(modified) if l.strip()]
tl = tp = tq = 0
print('## Added files (%d)' % len(A))
print('path | lines | max-line-chars | public | private | imports')
for p in A:
    n, w, pub, priv, kinds, imps = info(os.path.join(wt, p))
    tl += n; tp += pub; tq += priv
    print(f'{p} | {n} | {w} | {pub} | {priv} | ' + ', '.join(imps))
print(f'TOTAL added: {len(A)} files, {tl} lines, {tp} public, {tq} private declarations')
print()
print('## Modified files (%d)' % len(M))
print('path | lines before | lines after | public before/after | private before/after')
for p in M:
    nb, _, pb, qb, _, ib = info(os.path.join(before, p + '.txt'))
    na, _, pa, qa, _, ia = info(os.path.join(wt, p))
    print(f'{p} | {nb} | {na} | {pb}/{pa} | {qb}/{qa}')
    if ib != ia:
        print('   imports added:', [i for i in ia if i not in ib], 'removed:', [i for i in ib if i not in ia])
