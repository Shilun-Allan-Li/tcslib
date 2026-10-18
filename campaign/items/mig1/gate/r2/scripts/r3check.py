"""Confirm the R3 retirement sites at a worktree. Read-only.

Usage: python3 -I r3check.py <worktree> <r3-retirement.tsv>

For every row of the retirement table: the declaration line (`declared at`) holds a declaration
of the row, and every listed site line mentions it (a code site in code, a docstring site in a
comment or docstring). Prints one OK/BAD line per site and the summary
`r3: <ok> sites confirmed, <bad> mismatches`; exit code = number of mismatches.
"""
import os
import re
import sys

wt, tsv = sys.argv[1:3]
base = os.path.join(wt, 'TCSlib/Complexity')
cache = {}


def line(rel, n):
    # table paths are relative to TCSlib/Complexity/TuringMachine (`Build/…`) or name it
    path = rel if rel.startswith('TuringMachine/') else 'TuringMachine/' + rel
    if path not in cache:
        cache[path] = open(os.path.join(base, path), encoding='utf-8').read().split('\n')
    return cache[path][n - 1]


ok = bad = 0
rows = [l.split('\t') for l in open(tsv, encoding='utf-8').read().split('\n')[1:] if l.strip()]
for r in rows:
    names = [n.strip() for n in r[0].split(',')]
    if r[1] != '-':
        rel, n = r[1].split(':')
        t = line(rel, int(n))
        good = any(re.search(r'\btheorem\s+' + re.escape(x) + r'\b', t) for x in names)
        print(('OK ' if good else 'BAD'), 'declared', r[1], names)
        ok, bad = ok + good, bad + (not good)
    rel, rest = r[3].split(':', 1)
    for n in [int(x.strip().lstrip(':')) for x in rest.split(',')]:
        t = line(rel, n)
        good = any(x in t for x in names)
        if r[4] == 'code':
            good = good and not t.lstrip().startswith(('--', '/-', '*', '`')) and \
                any(re.search(r'(?<![\w`])' + re.escape(x) + r'\b', t.split('--')[0]) for x in names)
        print(('OK ' if good else 'BAD'), r[4], f'{rel}:{n}', names)
        ok, bad = ok + good, bad + (not good)
print(f'r3: {ok} sites confirmed, {bad} mismatches')
sys.exit(bad)
