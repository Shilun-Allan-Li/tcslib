"""Import-graph check of the landing tree (standard library only; python3 -I).

Usage: python3 -I graphcheck.py <worktree> <outdir>

Builds the TCSlib import graph of the worktree with every file of <outdir>/landing/ substituted
(new modules added), and checks that it is acyclic. Reports the core's closure, that neither
`Build/Loop` nor `Build/CounterLoop` is in it (so both can import it), and how many modules
newly have the core in their closure.
"""
import os
import re
import sys

WT, OUT = sys.argv[1], sys.argv[2]


def imports(path):
    return [m.group(1) for m in (re.match(r'^import\s+(\S+)', l)
                                 for l in open(path, encoding='utf-8')) if m]


def graph(root_files):
    g = {}
    for rel, path in root_files.items():
        mod = rel[:-5].replace('/', '.')
        g[mod] = [m for m in imports(path) if m.startswith('TCSlib')]
    return g


files = {}
for dp, dn, fn in os.walk(os.path.join(WT, 'TCSlib')):
    for f in fn:
        if f.endswith('.lean'):
            p = os.path.join(dp, f)
            files[os.path.relpath(p, WT)] = p
old = graph(files)
lroot = os.path.join(OUT, 'landing')
for dp, dn, fn in os.walk(lroot):
    for f in fn:
        if f.endswith('.lean'):
            p = os.path.join(dp, f)
            files[os.path.relpath(p, lroot)] = p
new = graph(files)

# Acyclicity (iterative DFS with colours).
WHITE, GREY, BLACK = 0, 1, 2
colour = {m: WHITE for m in new}
for root in sorted(new):
    if colour[root] != WHITE:
        continue
    stack = [(root, iter(new[root]))]
    colour[root] = GREY
    while stack:
        m, it = stack[-1]
        nxt = next(it, None)
        if nxt is None:
            colour[m] = BLACK
            stack.pop()
        elif nxt in new:
            if colour[nxt] == GREY:
                raise SystemExit(f'cycle through {nxt} (from {m})')
            if colour[nxt] == WHITE:
                colour[nxt] = GREY
                stack.append((nxt, iter(new[nxt])))


def closure(g, m):
    seen, todo = set(), [m]
    while todo:
        x = todo.pop()
        if x in seen or x not in g:
            continue
        seen.add(x)
        todo.extend(g[x])
    return seen - {m}


B = 'TCSlib.Complexity.TuringMachine.Build.Contract.Basic'
cb = closure(new, B)
print(f'modules: {len(old)} before, {len(new)} after; the substituted graph is acyclic')
print(f'closure of Contract.Basic ({len(cb)} TCSlib modules): {sorted(cb)}')
for m in ['TCSlib.Complexity.TuringMachine.Build.Loop',
          'TCSlib.Complexity.TuringMachine.Build.CounterLoop',
          'TCSlib.Complexity.TuringMachine.Build.Catalog',
          'TCSlib.Complexity.TuringMachine.Build.Embed',
          'TCSlib.Complexity.TuringMachine.Build.Seam',
          'TCSlib.Complexity.TuringMachine.Robustness.SingleTape']:
    print(f'  {m.split(".", 3)[-1]} in that closure: {m in cb} (so it can import the core: {m not in cb})')
users = [m for m in new if B in closure(new, m)]
print(f'modules with the core in their closure: {len(users)}')
for m in ['TCSlib.Complexity.TuringMachine.StateRenaming']:
    gained = sorted(closure(new, m) - closure(old, m))
    print(f'{m.split(".", 3)[-1]}: closure gains {gained}')
lc = closure(new, 'TCSlib.Complexity.TuringMachine.Build.Contract')
print(f'facade Build.Contract closure: {len(lc)} TCSlib modules; old landed file: '
      f'{len(closure(old, "TCSlib.Complexity.TuringMachine.Build.Contract"))}')
