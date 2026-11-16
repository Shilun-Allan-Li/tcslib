"""Compare control results with expectations (python3 -I).

Usage: check_controls.py <controls-dir>   (reads manifest.json's `expected` and results.jsonl)
Every row's error count (both `error:` and `error(` forms) must equal `expected`; every sealed
row must be harness-valid. Prints one line per row and ALL_OK or FAIL.
"""
import json
from pathlib import Path
import sys

folder = Path(sys.argv[1])
rows = [json.loads(l) for l in (folder / 'results.jsonl').read_text().splitlines() if l]
ok = True
for r in rows:
    good = r['error_count'] == r['expected'] and r.get('harness_valid', True)
    ok &= good
    print(f'{"OK  " if good else "FAIL"} {r["control"]:<12} {r["kind"]} {r["variant"]:<9} '
          f'errors={r["error_count"]} expected={r["expected"]} '
          f'harness={r.get("harness_valid", "n/a")}')
print('ALL_OK' if ok and rows else 'FAIL')
sys.exit(0 if ok and rows else 1)
