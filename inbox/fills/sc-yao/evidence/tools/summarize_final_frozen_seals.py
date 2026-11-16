#!/usr/bin/env python3
"""Validate resumed full-file seal coverage, source reconstruction and every diagnostic."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import runpy

lex = runpy.run_path('evidence/tools/header_lexer.py')
manifest = json.loads(Path('evidence/seals/final-frozen-files/final/manifest.json').read_text())
rows = []
for phase in ['final-frozen-files-1', 'final-frozen-files-resume4-1']:
    rows.extend(json.loads(s) for s in (Path('evidence/probe-runs') / phase /
                                      'results.jsonl').read_text().splitlines())
assert len(rows) == len(manifest) == 12
by_probe = {r['probe']: r for r in rows}
assert len(by_probe) == 12 and set(by_probe) == {r['probe'] for r in manifest}
summary = []
for m in manifest:
    row = by_probe[m['probe']]
    probe = Path(row['probe'])
    snap = Path(row['log']).with_suffix('.source.lean')
    assert probe.read_bytes() == snap.read_bytes()
    assert hashlib.sha256(snap.read_bytes()).hexdigest() == row['source_sha256']
    lines = snap.read_text().splitlines(keepends=True)
    start, count = row['original_insert_line'], row['inserted_lines']
    reconstructed = ''.join(lines[:start] + lines[start + count:])
    assert reconstructed == Path(row['file']).read_text(), row['file']
    raw = Path(row['log']).read_text()
    matches = list(re.finditer(r'^\S+\.lean:(\d+):(\d+): error[:(][^\n]*', raw, re.M))
    assert len(matches) == row['errors'] and row['generic_errors'] == 0
    declarations = lex['declarations'](snap.read_text())
    diagnostics = []
    for match in matches:
        line = int(match.group(1))
        offset = sum(map(len, lines[:line - 1]))
        owner = next((d['name'] for d in declarations
                      if d['start'] <= offset < d['end']), 'SEAL_PREAMBLE')
        diagnostics.append(dict(sealed_line=line, source_line=line - count,
            column=int(match.group(2)), declaration=owner, diagnostic=match.group(0)))
    stem = Path(row['file']).stem
    expected = 4 if stem == 'Uniform' else 24 if stem == 'Yao' and row['variant'] == 'B' else 0
    assert len(diagnostics) == expected
    assert row['exit'] == (1 if expected else 0)
    assert row['fresh_olean'] == (not expected)
    summary.append(dict(**row, unsealed_source_sha256=hashlib.sha256(
        reconstructed.encode()).hexdigest(), declaration_errors=diagnostics,
        failing_declarations=dict(Counter(d['declaration'] for d in diagnostics))))
out = Path('evidence/final-frozen-seal-summary.json')
assert not out.exists()
out.write_text(json.dumps(dict(checks=12, exact_coverage=True,
    exact_current_source_reconstruction=True, rows=summary,
    baseline_comparison='DAG0all; Uniform4all inherited; Yao A0/B15 at base. '
        'Final Yao B24=15base+2efficiency+7simulator-body; every error individually '
        'attributed in subagents/final-seal-attribution/ATTRIBUTION.json.'), indent=2) + '\n')
for r in summary:
    print(Path(r['file']).stem, r['variant'], r['coercions'], r['errors'],
          r['failing_declarations'])
