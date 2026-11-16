#!/usr/bin/env python3
"""Verify current-source seals, paired controls, and every stored constant's trace."""
import hashlib
import json
from pathlib import Path
import re
root = Path('evidence/subagents/b')
rows = []
for run in ['seals-01', 'followup-01']:
    rows += [json.loads(line) for line in (root/'probe-runs'/run/'results.jsonl').read_text().splitlines()]
seals = {}
for row in rows:
    if 'file' in row:
        seals[(row['file'], row['variant'], row['coercions'])] = row
assert len(seals) == 24
for row in seals.values():
    assert row['exit'] == row['errors'] == 0 and row['fresh_olean']
    assert row['source_sha256'] == hashlib.sha256(Path(row['probe']).read_bytes()).hexdigest()
controls = [r for r in rows if 'sealed' in r]
assert len(controls) == 8
for row in controls:
    assert row['errors'] == row['expected_errors']
    assert row['exit'] == (1 if row['sealed'] else 0)
traces = [r for r in rows if r['probe'].endswith('/AxiomsAndTrace.lean')]
assert len(traces) == 1 and traces[0]['exit'] == traces[0]['errors'] == 0
trace = Path(traces[0]['log']).read_text()
lines = [line.replace('\\t', '\t') for line in trace.splitlines()]
axioms = [line.split('\t', 2) for line in lines if line.startswith('AXIOMS\t')]
sorries = [line.split('\t', 2) for line in lines if line.startswith('SORRY_CLOSURE\t')]
count = int(re.search(r'STORED_CONSTANTS (\d+)', trace)[1])
assert len(axioms) == len(sorries) == count
assert all(row[2] == '[]' for row in sorries)
standard = {'propext', 'Classical.choice', 'Quot.sound'}
used = {a.strip() for row in axioms for a in row[2].strip('[]').split(',') if a.strip()}
assert used <= standard
base = json.loads((root/'seals/base/manifest.json').read_text())
assert len(base) == 6 and all(row['status'] == 'ABSENT_AT_BASE' for row in base)
summary = {'current_source_seals':len(seals), 'historical_seal_runs':sum('file' in r for r in rows),
           'all_current_source_seals_pass':True, 'paired_controls':len(controls),
           'sealed_controls_each_fail_exactly_once':True, 'stored_constants':count,
           'axioms':sorted(used), 'sorry_dependencies':[], 'base_files_absent':len(base)}
(root/'verification-summary.json').write_text(json.dumps(summary, indent=2)+'\n')
(root/'current-source-seals.json').write_text(json.dumps(list(seals.values()), indent=2)+'\n')
print(json.dumps(summary, indent=2))
