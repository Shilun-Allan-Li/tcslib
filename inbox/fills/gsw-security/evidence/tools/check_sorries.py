"""Admissions: compare the sweep's `declaration uses 'sorry'` warnings with base-sorries.txt.

Usage (python3 -I, from the fill checkout root):
    check_sorries.py <order.txt> <sweep-log-dir> <base-sorries.txt> <expected-removed ...>
Each warning `<file>:<line>:<col>: warning: declaration uses 'sorry'` is mapped to the
declaration declared at that line of the source (namespace-relative name, as in
base-sorries.txt). Prints the current admissions in base-sorries format, then the diff
against the base list, and checks that exactly the expected targets were removed and
nothing was added.
"""
import re
import sys
from pathlib import Path

order, logdir, basefile = sys.argv[1], Path(sys.argv[2]), sys.argv[3]
expected = set(sys.argv[4:])
DECL = re.compile(r'(?:theorem|lemma|def|abbrev|instance)\s+(\S+)')


def short(m):
    return m.removeprefix('TCSlib/Complexity/').removeprefix('TCSlib/')


current = {}
for m in [l.strip() for l in open(order) if l.strip()]:
    log = logdir / (m.replace('/', '_') + '.log')
    text = log.read_text()
    src = Path(m + '.lean').read_text().split('\n')
    names = []
    for w in re.finditer(r'^\S+\.lean:(\d+):\d+: warning: declaration uses .sorry.', text, re.M):
        line = src[int(w[1]) - 1]
        d = DECL.search(line)
        names.append(d[1] if d else f'?line{w[1]}')
    if names:
        current[m] = names
base = {}
for line in open(basefile):
    if line.startswith('TOTAL') or not line.strip():
        continue
    mod, n, rest = line.split(':', 2)
    base[mod.strip()] = [x.strip() for x in rest.split(',')]
cur_short = {}
for m, names in current.items():
    key = m.removeprefix('TCSlib/Complexity/') if m.startswith('TCSlib/Complexity/') else m
    cur_short[key] = names
print('# current admissions (base-sorries format)')
for m, names in cur_short.items():
    print(f'{m}: {len(names)}: {", ".join(names)}')
total = sum(map(len, cur_short.values()))
print(f'TOTAL {total} in {len(cur_short)} modules')
bset = {(m, n) for m, ns in base.items() for n in ns}
cset = {(m, n) for m, ns in cur_short.items() for n in ns}
removed, added = sorted(bset - cset), sorted(cset - bset)
print('# removed since base:')
for r in removed:
    print(f'  - {r[0]}: {r[1]}')
print('# added since base:')
for a in added:
    print(f'  + {a[0]}: {a[1]}')
ok = {n for _, n in removed} == expected and len(removed) == len(expected) and not added
print(f'ADMISSIONS base={len(bset)} current={len(cset)} removed={len(removed)} '
      f'added={len(added)} expected_removed={len(expected)} -> {"PASS" if ok else "FAIL"}')
sys.exit(0 if ok else 1)
