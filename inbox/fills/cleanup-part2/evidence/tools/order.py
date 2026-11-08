#!/usr/bin/env python3
"""Topological order of all TCSlib modules (root prerequisites, root excluded) from the current
source imports, deterministic: Kahn's algorithm with ties broken by the issued
root-prerequisites order (new/changed import edges respected). python3 -I order.py <out.txt>"""
import sys, os, re, heapq
ROOT = '/workspace/cp2/src'
src = open('/workspace/cp2/tools/chk.py').read()
exec(src.split('def header_imports')[1].split('imports = header_imports')[0].join(['def header_imports', '']))
base = [l.strip() for l in open('/workspace/tcslib/outbox/fills/cleanup-part2/inputs/orders/root-prerequisites-order.txt') if l.strip()]
rank = {m: i for i, m in enumerate(base)}
mods = set(base)
deps = {}
for m in mods:
    imps = [x.replace('.', '/') for x in header_imports(open(f'{ROOT}/{m}.lean').read()) if x.startswith('TCSlib')]
    deps[m] = [x for x in imps if x in mods]
indeg = {m: len(set(deps[m])) for m in mods}
rev = {m: [] for m in mods}
for m in mods:
    for d in set(deps[m]): rev[d].append(m)
h = [(rank[m], m) for m in mods if indeg[m] == 0]; heapq.heapify(h); out = []
while h:
    _, m = heapq.heappop(h); out.append(m)
    for x in rev[m]:
        indeg[x] -= 1
        if indeg[x] == 0: heapq.heappush(h, (rank[x], x))
assert len(out) == len(mods), 'cycle'
open(sys.argv[1], 'w').write('\n'.join(out) + '\n')
print(len(out), 'modules; differs from issued order:', out != base)
