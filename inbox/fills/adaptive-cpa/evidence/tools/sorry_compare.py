"""Compare a sweep's `declaration uses 'sorry'` warnings with base-sorries.txt.

Each warning's line is mapped to the declaration name written on that source line.
Usage (from the clone): python3 -I sorry_compare.py <sweep.tsv> <sweep-log-dir> <base-sorries.txt>
(sweep.tsv rows: module, exit, seconds, max RSS, sorry count; logs named <module with dots>.log)
"""
import re
import sys
from pathlib import Path

tsv, logdir, basefile = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3])
base = {}
for line in basefile.read_text().splitlines():
    if line.startswith('TOTAL') or not line.strip():
        continue
    mod, cnt, names = line.split(': ', 2)
    base[mod] = sorted(n.strip() for n in names.split(','))
now = {}
for row in tsv.read_text().splitlines():
    mod = row.split('\t')[0]
    log = logdir / (mod.replace('/', '.') + '.log')
    src = Path(mod + '.lean').read_text(encoding='utf-8').splitlines()
    names = []
    for m in re.finditer(r"^" + re.escape(mod) + r"\.lean:(\d+):\d+: warning: declaration uses 'sorry'",
                         log.read_text(encoding='utf-8'), re.M):
        text = src[int(m.group(1)) - 1]
        d = re.search(r'(?:theorem|lemma|def|instance|abbrev)\s+([^\s(:]+)', text)
        names.append(d.group(1) if d else f'?line{m.group(1)}')
    if names:
        now[mod] = sorted(names)
def key(mod):
    for b in base:
        if mod == b or mod.endswith('/' + b) or mod == 'TCSlib/Complexity/' + b:
            return b
    return None
total_now = sum(len(v) for v in now.values())
total_base = sum(len(v) for v in base.values())
print(f'base admissions: {total_base}; sweep admissions: {total_now}')
seen = set()
removed, added = [], []
for mod, names in sorted(now.items()):
    b = key(mod)
    bn = base.get(b, [])
    seen.add(b)
    print(f'{mod}: {len(names)}: {", ".join(names)}')
    added += [(mod, n) for n in names if n not in bn]
    removed += [(mod, n) for n in bn if n not in names]
for b, bn in base.items():
    if b not in seen:
        removed += [(b, n) for n in bn]
print('removed relative to base:', removed)
print('added relative to base:', added)
