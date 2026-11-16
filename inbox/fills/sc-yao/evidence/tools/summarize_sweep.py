#!/usr/bin/env python3
"""Validate exact sweep coverage, source hashes and admitted-declaration differences."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy

p = argparse.ArgumentParser()
p.add_argument('--phase', required=True)
p.add_argument('--order', required=True)
p.add_argument('--removed', nargs='+', required=True)
p.add_argument('--output', required=True)
a = p.parse_args()
lex = runpy.run_path('evidence/tools/header_lexer.py')
order = Path(a.order).read_text().splitlines()
rows = [json.loads(s) for s in
        (Path('evidence/logs') / a.phase / 'results.jsonl').read_text().splitlines()]
assert [r['module'] for r in rows] == order
warnings = []
for row in rows:
    assert row['exit'] == row['errors'] == row['generic_errors'] == 0, row
    assert row['fresh_olean'], row
    snap = Path(row['source'])
    source = snap.read_text()
    assert hashlib.sha256(snap.read_bytes()).hexdigest() == row['source_sha256']
    assert snap.read_bytes() == Path(row['module'] + '.lean').read_bytes()
    ds = lex['declarations'](source)
    raw = Path(row['log']).read_text()
    for line in re.findall(r"^\S+\.lean:(\d+):\d+: warning: declaration uses 'sorry'", raw, re.M):
        offset = sum(len(s) + 1 for s in source.splitlines()[:int(line) - 1])
        d = next(d for d in ds if d['start'] <= offset < d['end'])
        warnings.append(dict(module=row['module'], name=d['name'], line=int(line),
                             log=row['log']))
actual = {(r['module'], r['name']) for r in warnings}
expected = set()
for line in Path('evidence/inputs/base-sorries.txt').read_text().splitlines():
    if line.startswith('TOTAL'):
        continue
    module, number, names = line.split(': ', 2)
    if not module.startswith('TCSlib/'):
        module = 'TCSlib/Complexity/' + module
    expected.update((module, name) for name in names.split(', '))
removed, added = expected - actual, actual - expected
assert removed == {('TCSlib/Cryptography/SecureComputation/Yao', n) for n in a.removed}
assert not added, added
assert len(warnings) == len(expected) - len(a.removed)
out = Path(a.output)
assert not out.exists(), out
out.write_text(json.dumps(dict(modules=len(rows), errors=0, exact_source_hashes=True,
    base_sorry_declarations=len(expected), current_sorry_declarations=len(actual),
    removed=sorted(removed), added=sorted(added), warnings=warnings), indent=2) + '\n')
print(f'{len(rows)} MODULES PASS; {len(actual)} ADMITTED DECLARATIONS; REMOVED {a.removed}')
