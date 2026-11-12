#!/usr/bin/env python3
"""Compare two declaration dumps (DeclDump output): rows `name | module | kind | type hash | attrs | axioms`.
Usage: cmpdump.py <base.log> <final.log> [module-filter-file]
Prints removed, added, changed (type hash, kind or attributes), moved (same name/type, other
module) and axiom changes, restricted to names whose base or final module is in the filter
(default: every module that appears in both dumps' candidate lists)."""
import sys, re

def load(p):
    rows = {}
    for l in open(p):
        parts = [x.strip() for x in l.rstrip('\n').split(' | ')]
        if len(parts) != 6:
            continue
        n, m, k, h, a, ax = parts
        rows[n] = dict(module=m, kind=k, hash=h, attrs=a, axioms=ax)
    return rows

b, f = load(sys.argv[1]), load(sys.argv[2])
mods = None
if len(sys.argv) > 3:
    mods = set(l.strip() for l in open(sys.argv[3]) if l.strip())
def keep(n, d):
    return mods is None or d['module'] in mods
bn = {n for n, d in b.items() if keep(n, d)}
fn = {n for n, d in f.items() if keep(n, d)}
removed = sorted(bn - set(f))
added = sorted(fn - set(b))
changed, moved, axch = [], [], []
for n in sorted((bn | fn) & set(b) & set(f)):
    x, y = b[n], f[n]
    if (x['hash'], x['kind'], x['attrs']) != (y['hash'], y['kind'], y['attrs']):
        changed.append((n, x, y))
    elif x['module'] != y['module']:
        moved.append((n, x['module'], y['module']))
    if x['axioms'] != y['axioms']:
        axch.append((n, x['axioms'], y['axioms']))
print(f'base rows: {len(bn)}  final rows: {len(fn)}')
print(f'REMOVED ({len(removed)})')
for n in removed:
    print(f'  - {n} | {b[n]["module"]} | {b[n]["kind"]}')
print(f'ADDED ({len(added)})')
for n in added:
    print(f'  + {n} | {f[n]["module"]} | {f[n]["kind"]}')
print(f'MOVED, same type and attributes ({len(moved)})')
for n, a, c in moved:
    print(f'  > {n} | {a} -> {c}')
print(f'CHANGED type/kind/attributes ({len(changed)})')
for n, x, y in changed:
    print(f'  ! {n} | {x["module"]} {x["kind"]} {x["hash"]} {x["attrs"]} -> {y["module"]} {y["kind"]} {y["hash"]} {y["attrs"]}')
print(f'AXIOMS CHANGED ({len(axch)})')
for n, a, c in axch:
    print(f'  ~ {n} | {a} -> {c}')
axs = {}
for n in fn:
    axs.setdefault(f[n]['axioms'], 0)
    axs[f[n]['axioms']] += 1
print('FINAL AXIOM SETS:', axs)
