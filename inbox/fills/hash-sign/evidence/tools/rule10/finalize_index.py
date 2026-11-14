"""Validate closed final evidence and write a compact index; no Lean execution."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--root', type=Path, default=Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence'))
p.add_argument('--repo', type=Path, default=Path('/private/tmp/hash-sign-fill/repo'))
p.add_argument('--rev', default='2e9d455a003c83d33b89149c83a6ab0610a63a4f')
args = p.parse_args()
final = args.root / 'rule10/final-r2'
load = lambda path: json.loads(path.read_text())
matrix = load(final / 'seal-matrix.json')
controls = load(final / 'control-audit-summary.json')
axioms = load(final / 'axioms-summary.json')
explicit = load(final / 'explicit-final.json')
review = load(final / 'explicit-review.json')
failures = load(args.root / 'rule10/source-seal-failure-ledger.json')
assert matrix['complete'] and matrix['passed_cells'] == 20 and matrix['latest_source_commit'] == args.rev
assert controls['all_expectations_and_native_guard_coverage_passed'] and controls['control_probes'] == 22
assert controls['unsealed'] == controls['sealed_negatives_each_exactly_one_error'] == 11
assert axioms['stored_constants'] == 176 and len(axioms['target']) == 1
assert set(axioms['target'][0]['axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
assert explicit['summary']['foreign_items'] == 0
assert review['original_unresolved_count'] == review['public_theorem_alias_items'] + review['local_proof_items']
assert failures['source_seal_diagnostics'] == 3 and failures['all_have_latest_byte_passing_resolution']
alias_log = (args.root / 'logs/rule10-final-r2-explicit-aliases-1.log').read_text()
actual_aliases = {l.split(' ', 1)[1] for l in alias_log.splitlines() if l.startswith('EXPLICIT_ALIAS_THEOREM ')}
assert actual_aliases == set(review['native_theorem_targets'])
kind_log = (args.root / 'logs/rule10-final-r2-explicit-kinds-1.log').read_text()
expected_candidates = int(re.search(r'candidates (\d+)', (final / 'explicit-prepare.log').read_text())[1])
assert re.findall(r'EXPLICIT_KIND_DONE (\d+)', kind_log) == [str(expected_candidates)]
base_facade = args.root / 'rule10/base-facade-2250'
for letter in 'AB':
    status = load(base_facade / ('run-' + letter + '-status.json'))
    assert status['stage'] == 'complete' and status['all_proofs_passed'] and status['all_native_guard_coverage_verified']
base_scope = []
for owner in (final / 'owners.txt').read_text().splitlines():
    path = owner.replace('.', '/') + '.lean'
    result = subprocess.run(['git', '--no-optional-locks', '-C', str(args.repo), 'cat-file', '-e',
              'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9:' + path], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    base_scope.append({'owner': owner, 'exists_at_base': result.returncode == 0,
                       'baseline_disposition': 'checked' if result.returncode == 0 else 'not present at base; no fabricated baseline check'})
logs = {}
for results in (args.root / 'rule10').rglob('results.jsonl'):
    for line in results.read_text().splitlines():
        result = json.loads(line)
        log = Path(result['raw_log'])
        assert log.is_file()
        text = log.read_text()
        assert re.search(r'end: .* exit: -?\d+\s*$', text), str(log)
        raw = log.read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        assert digest == result['raw_log_sha256'], str(log)
        logs[log.relative_to(args.root).as_posix()] = {'bytes': len(raw), 'sha256': digest}
index = {'latest_source_commit': args.rev, 'native_work_closed': True, 'final_owner_variant_cells': 20,
         'all_final_seals_passed': True, 'stored_constant_axioms': 176, 'target_axioms': axioms['target'][0]['axioms'],
         'remaining_nonstandard_axioms': axioms['outside_standard_axioms'],
         'final_controls': {'pairs': 11, 'probes': 22, 'unsealed_passed': 11, 'sealed_negatives_each_exactly_one_error': 11,
              'reader_positives_clean': True, 'native_guard_audits': 11},
         'explicit_scan': {'items': explicit['summary']['items'], 'public_theorem_uses': explicit['summary']['by_class']['THEOREM'] + review['public_theorem_alias_items'],
              'owned_definition_uses': explicit['summary']['by_class']['OWNED_DEFINITION'], 'local_proof_names': review['local_proof_items'],
              'foreign_definition_uses': 0, 'native_lookup_candidates': expected_candidates},
         'historical_source_failures': {'diagnostics': 3, 'all_resolved': True, 'ledger': 'rule10/source-seal-failure-ledger.json'},
         'base_scope': base_scope,
         'baseline_facade_limitation': load(base_facade / 'catalog-reconstruction.json')['limitation'],
         'key_files': ['rule10/final-r2/seal-matrix.json', 'rule10/final-r2/axioms-summary.json',
               'rule10/final-r2/explicit-final.json', 'rule10/final-r2/explicit-review.json',
               'rule10/final-r2/control-audit-summary.json', 'rule10/base/summary.json',
               'rule10/base-facade-2250/catalog-reconstruction.json', 'rule10/final-r2/reused-B-justification.json'],
         'closed_probe_raw_logs': logs}
(args.root / 'rule10/FINAL-INDEX.json').write_text(json.dumps(index, indent=2) + '\n')
(args.root / 'rule10/closed-probe-log-list.txt').write_text(''.join(p + '\n' for p in sorted(logs)))
print(json.dumps({k: v for k, v in index.items() if k not in ['closed_probe_raw_logs','base_scope','key_files']}))
print('closed probe raw logs:', len(logs))
