"""Summarize final source, full-file seal, normal, and stored-constant checks."""
import hashlib
import json
from pathlib import Path
import re

root = Path('evidence/subagents/b6')
modules = json.loads((root / 'final-modules.json').read_text())
error_re = re.compile(r'^\S+\.lean:\d+:\d+: error[:(]', re.M)
def records(run):
    return [json.loads(line) for line in
            (root / 'probe-runs' / run / 'results.jsonl').read_text().splitlines()]
def good(rows, count):
    assert len(rows) == count, (len(rows), count)
    assert all(r['exit'] == 0 and r['errors'] == 0 and r['fresh_olean'] for r in rows)
seals = records('final01')
normals = records('normal-final01')
trace = records('trace-final01')
good(seals, 4)
good(normals, 1)
good(trace, 1)
summary = {'modules': [], 'seals': seals, 'normals': normals, 'trace': trace,
           'history': [], 'seal_profile_differences': []}
for name in modules:
    source = Path('TCSlib/Cryptography/SecureComputation/Yao/HybridProof') / (name + '.lean')
    raw = source.read_bytes()
    text = raw.decode()
    wide = [i for i, line in enumerate(text.splitlines(), 1) if len(line) > 100]
    admissions = re.findall(r'\b(?:sorry|admit|axiom)\b', text)
    assert not wide and len(text.splitlines()) < 1000 and not admissions
    normal = next(r for r in normals if Path(r['probe']).stem == name)
    assert normal['source_sha256'] == hashlib.sha256(raw).hexdigest()
    artifact = Path('.lake/sc-yao-oleans') / source.with_suffix('.olean')
    summary['modules'].append({'module': name, 'source': str(source),
        'lines': len(text.splitlines()), 'source_sha256': hashlib.sha256(raw).hexdigest(),
        'olean_sha256': hashlib.sha256(artifact.read_bytes()).hexdigest(),
        'width_violations': wide, 'textual_admissions': admissions})
    profiles = {}
    for row in (r for r in seals if Path(r['file']).stem == name):
        probe = Path(row['probe'])
        snap = root / 'probe-runs' / 'final01' / (probe.stem + '.source.lean')
        assert hashlib.sha256(snap.read_bytes()).hexdigest() == row['source_sha256']
        lines = snap.read_text().splitlines(keepends=True)
        k = row['original_insert_line']
        restored = ''.join(lines[:k] + lines[k + row['inserted_lines']:])
        assert restored.encode() == raw, name
        log = Path(row['log']).read_text()
        profiles[(row['variant'], row['coercions'])] = set(
            re.findall(r'^EXCLUDED\t[^\t]+\t([^\n]+)', log, re.M))
    for variant in ['A', 'B']:
        delta = profiles[(variant, 'coe')] - profiles[(variant, 'strict')]
        summary['seal_profile_differences'].append({'module': name, 'variant': variant,
            'projection_coercions_excluded_only_in_coe': sorted(delta)})
    for coe in ['strict', 'coe']:
        delta = profiles[('A', coe)] - profiles[('B', coe)]
        assert delta <= {'Complexity.PolyExpr.eval'}, (name, coe, delta)
        summary['seal_profile_differences'].append({'module': name, 'coercions': coe,
            'polyExpr_eval_notation_only_in_A': sorted(delta)})
log = Path(trace[0]['log']).read_text()
closures = re.findall(r'^SORRY_CLOSURE\t([^\t]+)\t(\[[\s\S]*?\])', log, re.M)
axioms = re.findall(r'^AXIOMS\t([^\t]+)\t(\[[\s\S]*?\])', log, re.M)
count = int(re.search(r'STORED_CONSTANTS (\d+)', log).group(1))
assert len(closures) == len(axioms) == count
assert all(body == '[]' for _, body in closures)
used_axioms = set()
for _, body in axioms:
    used_axioms.update(re.findall(r'[A-Za-z_][A-Za-z0-9_.]*', body))
assert used_axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, used_axioms
summary['stored_constants'] = count
summary['axioms'] = sorted(used_axioms)
summary['sorry_closures_nonempty'] = []
for path in sorted(root.glob('*.log')):
    text = path.read_text()
    summary['history'].append({'log': str(path), 'errors_both_forms': len(error_re.findall(text)),
                              'checker_failure_marker': 'FAIL(' in text})
(root / 'final-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('PASS', len(modules), 'modules;', len(seals), 'seals;', count, 'stored constants;',
      'axioms', sorted(used_axioms))
