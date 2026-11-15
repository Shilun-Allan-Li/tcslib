"""Validate final source provenance, scope, and all-constant axiom evidence."""
import hashlib
import json
from pathlib import Path
import subprocess

tip = '5e12a169e671dc16b6766e21067b79c16835af67'
base = '01de2d8baed9113e4a099e13c5d50c81e6dbc66f'
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip() == tip
rows = [json.loads(line) for line in Path('evidence/logs/final-full/results.jsonl').read_text().splitlines()]
order = Path('evidence/logs/final-order.txt').read_text().splitlines()
assert len(rows) == 387 and [row['module'] for row in rows] == order
for row in rows:
    assert row['exit'] == 0 and row['errors'] == 0, row
    source = subprocess.check_output(['git', 'show', tip + ':' + row['module'] + '.lean'])
    assert hashlib.sha256(source).hexdigest() == row['source_sha256'], row['module']
changed = subprocess.check_output(['git', 'diff', '--name-only', base, tip], text=True).splitlines()
allowed = {'TCSlib/Complexity/ClassP/DTIME.lean',
           'TCSlib/Complexity/Randomized/Build/IterateFind.lean',
           'TCSlib/Complexity/Randomized/Classes.lean',
           'TCSlib/Complexity/Randomized/SeedMajority.lean',
           'TCSlib/Cryptography/Randomness/Derandomization.lean'}
assert len(changed) == 15
assert all(path in allowed or path.startswith((
    'TCSlib/Complexity/Randomized/SeedMajority/',
    'TCSlib/Cryptography/Randomness/Derandomization/')) for path in changed)
census = Path('evidence/logs/final-replay-axioms/evidence_axioms_final_Census.log').read_text()
constants = [json.loads(line.split(' ', 1)[1]) for line in census.splitlines()
             if line.startswith('DERAND-AXIOMS ')]
standard = {'propext', 'Classical.choice', 'Quot.sound'}
assert constants and all(set(row['axioms']) <= standard for row in constants)
by_name = {row['name']: row for row in constants}
required = ['Complexity.exists_seedMajorityTM', 'Complexity.seedMajority_mem_DTIME',
    'TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp',
    'Complexity.IterateFind.computesFunInTime_find', 'Complexity.mem_DTIME_iff',
    'Turing.FinTM.decidesInTime_iff', 'Randomized.inBPP_iff',
    'Complexity.IterateFind.polyTimeComputable_find', 'Complexity.polyTimeComputable_iterateFind']
assert all(name in by_name for name in required)
baseline = Path('evidence/logs/base-axioms/evidence_axioms_base_Census.log').read_text()
base_constants = {row['name']: row for row in (json.loads(line.split(' ', 1)[1])
    for line in baseline.splitlines() if line.startswith('DERAND-AXIOMS '))}
for name in ['Complexity.IterateFind.polyTimeComputable_find', 'Complexity.polyTimeComputable_iterateFind']:
    assert set(by_name[name]['axioms']) == set(base_constants[name]['axioms']), name
out = dict(tip=tip, modules=387, zero_errors=True, every_source_hash_matches_tip=True,
           changed_files=changed, stored_constants=len(constants), standard_axioms_only=True,
           original_find_and_consumer_axioms_identical=True)
Path('evidence/logs/final-validation.json').write_text(json.dumps(out, indent=2) + '\n')
print(f'FINAL VALIDATION PASS: 387 exact final sources; 0 errors; '
      f'{len(constants)} stored constants with only standard axioms; 15 permitted source files')
