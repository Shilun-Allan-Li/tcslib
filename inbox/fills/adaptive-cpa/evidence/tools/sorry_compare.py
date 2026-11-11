"""Compare the sweep's `declaration uses 'sorry'` warnings with base-sorries.txt.

Each warning's line is mapped to the declaration name written on that source line.
Usage (from the clone): python3 -I sorry_compare.py <sweep.tsv> <sweep-log-dir> <base-sorries.txt>
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
    idx, mod, rc = row.split('\t')
    log = next(logdir.glob(f'{idx}-*.log'))
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
matched = set()
print(f'base admissions: {total_base}; sweep admissions: {total_now}')
for mod, names in now.items():
    b = key(mod)
    matched.add(b)
    old = base.get(b, [])
    removed = sorted(set(n.split('.')[-1] for n in old) - set(n.split('.')[-1] for n in names))
    added = sorted(set(n.split('.')[-1] for n in names) - set(n.split('.')[-1] for n in old))
    status = 'same' if not removed and not added and len(old) == len(names) else f'removed={removed} added={added}'
    print(f'{mod}: {len(names)} (base {len(old)}) {status}')
for b in base:
    if b not in matched:
        print(f'{b}: 0 (base {len(base[b])}) removed={base[b]}')
