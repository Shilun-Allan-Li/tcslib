#!/usr/bin/env python3
"""Combine unchanged source checks with four exact-source documentation reruns."""
import hashlib
import json
from pathlib import Path

runs = ['final-helper-seals-' + str(i) for i in range(3)]
runs.append('final-publication-garbling-1')
rows = []
for run in runs:
    rows.extend(json.loads(s) for s in (Path('evidence/probe-runs') / run /
                                      'results.jsonl').read_text().splitlines())
assert len(rows) == 276
current, superseded = {}, []
for row in rows:
    key = row['file'], row['variant'], row['coercions']
    if key in current:
        assert row['file'].endswith('/HybridProof/Garbling.lean')
        superseded.append(current[key])
    current[key] = row
assert len(current) == 272 and len(superseded) == 4
files = {str(p) for p in Path(
    'TCSlib/Cryptography/SecureComputation/Yao/HybridProof').glob('*.lean')}
files.add('TCSlib/Cryptography/SecureComputation/Yao/HybridProof.lean')
assert {r['file'] for r in current.values()} == files
assert set(current) == {(f, v, c) for f in files for v in ['A', 'B']
                        for c in ['strict', 'coe']}
for row in current.values():
    assert row['exit'] == row['errors'] == row['generic_errors'] == 0
    assert row['fresh_olean'] and row['read_only_import_lock']
    snapshot = Path(row['log']).with_suffix('.source.lean')
    assert hashlib.sha256(snapshot.read_bytes()).hexdigest() == row['source_sha256']
    assert snapshot.read_bytes() == Path(row['probe']).read_bytes()
    lines = snapshot.read_text().splitlines(keepends=True)
    start, n = row['original_insert_line'], row['inserted_lines']
    original = ''.join(lines[:start] + lines[start+n:])
    assert original == Path(row['file']).read_text(), row['file']
out = Path('evidence/final-current-helper-seal-summary.json')
assert not out.exists()
out.write_text(json.dumps(dict(checks=272, raw_completed_checks=276, files=68,
    all_pass=True, exact_current_source_reconstruction=True,
    unchanged_source_rows=268, current_garbling_rows=4,
    superseded_rows=superseded, rows=sorted(current.values(),
        key=lambda r: (r['file'], r['variant'], r['coercions']))), indent=2) + '\n')
print('CURRENT SOURCE:272/272helpersealsPASS;4historicalrowsretained;276rawruns')
