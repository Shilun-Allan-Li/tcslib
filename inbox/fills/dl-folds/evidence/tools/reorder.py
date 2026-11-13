#!/usr/bin/env python3
"""Recompute the check order after import changes.

Usage: reorder.py BASE_ORDER OUT_ORDER [NEW_MODULE ...]

Stable topological sort of the modules of BASE_ORDER plus the new modules, on their TCSlib
imports as found in the working tree (/workspace/folds): among the modules whose imports are all
placed, the one earliest in the base order goes first. A new module takes the position of its
first consumer (just before it). Prints the moves relative to the base order.
"""
import heapq, re, sys

ROOT = "/workspace/folds"
base = [l.strip() for l in open(sys.argv[1]) if l.strip()]
new = sys.argv[3:]
mods = base + [m for m in new if m not in base]


def imports(m):
    out = []
    for line in open(f"{ROOT}/{m}.lean"):
        mm = re.match(r"^import\s+(TCSlib\S*)", line)
        if mm:
            out.append(mm.group(1).replace(".", "/"))
    return out


deps = {m: [d for d in imports(m) if d in set(mods)] for m in mods}
missing = {m: [d for d in imports(m) if d not in set(mods)] for m in mods}
for m, ds in missing.items():
    if ds:
        print(f"WARNING {m} imports modules outside the order: {ds}", file=sys.stderr)
users = {m: [] for m in mods}
for m, ds in deps.items():
    for d in ds:
        users[d].append(m)
prio = {m: float(i) for i, m in enumerate(base)}
for m in new:
    if m not in prio:
        cons = [prio[u] for u in users[m] if u in prio]
        prio[m] = (min(cons) - 0.5) if cons else float(len(base))
indeg = {m: len(set(deps[m])) for m in mods}
heap = [(prio[m], m) for m in mods if indeg[m] == 0]
heapq.heapify(heap)
out = []
while heap:
    _, m = heapq.heappop(heap)
    out.append(m)
    for u in set(users[m]):
        indeg[u] -= 1
        if indeg[u] == 0:
            heapq.heappush(heap, (prio[u], u))
assert len(out) == len(mods), "import cycle"
open(sys.argv[2], "w").write("\n".join(out) + "\n")
pos = {m: i for i, m in enumerate(out)}
for i, m in enumerate(base):
    if pos[m] != i:
        pass
moved = [m for m in out if m in base and
         [x for x in out if x in base].index(m) != base.index(m)]
print(f"{len(out)} modules; new: {[m for m in out if m not in base]}")
for m in new:
    print(f"NEW {m} at {pos[m] + 1}")
for m in base:
    if base.index(m) != [x for x in out if x in base].index(m):
        print(f"MOVED {m}: {base.index(m) + 1} -> {pos[m] + 1}")
