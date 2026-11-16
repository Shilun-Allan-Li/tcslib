"""Count `error:` and `error(` diagnostics (G26-N1) in every .log under the given dirs (python3 -I).
Usage: error_counts.py <dir> [...]  One line per log with errors, plus per-dir totals."""
import re, sys
from pathlib import Path
pat = re.compile(r'^\S+\.lean:\d+:\d+: error([:(])', re.M)
for d in sys.argv[1:]:
    logs = sorted(Path(d).rglob('*.log'))
    tc = tp = 0
    for p in logs:
        found = pat.findall(p.read_text())
        c, q = found.count(':'), found.count('(')
        tc += c; tp += q
        if c or q:
            print(f'  {p}: error:={c} error(={q}')
    print(f'{d}: {len(logs)} logs, error:={tc}, error(={tp}')
