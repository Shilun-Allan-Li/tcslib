import datetime
import gzip
import hashlib
import json
import pathlib
import subprocess

repo = pathlib.Path('/private/tmp/hash-sign-fill/repo')
ev = pathlib.Path('/private/tmp/hash-sign-fill/delivery/hash-sign/evidence')
def read(rel):
    return json.loads((ev/rel).read_text())
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
commit = subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
index = read('rule10/FINAL-INDEX.json')
assert index['latest_source_commit'] == commit and index['native_work_closed']
assert index['all_final_seals_passed'] and index['final_owner_variant_cells'] == 20
for name, info in index['closed_probe_raw_logs'].items():
    p = ev/name
    assert p.stat().st_size == info['bytes'] and sha(p) == info['sha256'], name
scope = read('logs/source-scope.json')
assert scope['commit'] == commit and scope['scope_pass'] and scope['target_header_identical']
assert scope['other_original_declarations_identical']
source_hashes = {p['path'][:-5].replace('/','.'):p['sha256'] for p in scope['files']}
matrix = read('rule10/final-r2/seal-matrix.json')
assert matrix['complete'] and matrix['passed_cells'] == matrix['expected_cells'] == 20
assert matrix['latest_source_commit'] == commit
requests = {}
for cell in matrix['matrix']:
    owner, variant = cell['owner'], cell['variant']
    assert cell['passed'] and cell['latest_source_sha256'] == source_hashes[owner]
    candidates = [r for r in cell['actual_checks'] if r['matches_latest_source_bytes'] and r['proof_and_full_guard_coverage_passed']]
    assert candidates, (owner,variant)
    for r in candidates:
        record_path, log_path, audit_path = map(pathlib.Path, [r['request_record'],r['raw_log'],r['guard_audit']])
        record, audit = json.loads(record_path.read_text()), json.loads(audit_path.read_text())
        assert record['source_sha256'] == source_hashes[owner]
        assert audit['native_identity_install_mask_eof_complete'] and audit['proof_error_diagnostics'] == 0
        assert audit['record_sha256'] == sha(record_path) and audit['raw_log_sha256'] == sha(log_path)
        assert record['requested'] == len(record['rows']) == audit['request_count']
        requests[owner,variant] = record['requested']
for owner in source_hashes:
    assert requests[owner,'B'] == requests[owner,'A'] + 1
controls = read('rule10/final-r2/control-audit-summary.json')
assert controls['control_probes'] == 22 and controls['unsealed'] == 11
assert controls['sealed_negatives_each_exactly_one_error'] == 11
assert controls['all_expectations_and_native_guard_coverage_passed']
for variant in ['A','B']:
    status = read('rule10/base-facade-2250/run-'+variant+'-status.json')
    assert status['stage'] == 'complete' and status['all_proofs_passed'] and status['all_native_guard_coverage_verified']
base = read('rule10/base/summary.json')
assert base['all_control_expectations_passed'] and base['all_pairs_complete_and_passed']
axioms = read('rule10/final-r2/axioms-summary.json')
assert axioms['stored_constants'] == 176
assert set(axioms['target'][0]['axioms']) == {'propext','Classical.choice','Quot.sound'}
assert len(axioms['outside_standard_axioms']) == 1
assert axioms['outside_standard_axioms'][0]['name'].endswith('.exists_oneTimeSecure_of_crh_owf')
assert index['explicit_scan']['items'] == 406 and index['explicit_scan']['foreign_definition_uses'] == 0
assert index['explicit_scan']['public_theorem_uses'] + index['explicit_scan']['owned_definition_uses'] + index['explicit_scan']['local_proof_names'] == 406
sweep, admissions, lint, reproduction = [read('logs/'+n+'.json') for n in ['sweep-summary','admission-delta','lint-delta','patch-reproduction']]
assert sweep['passed'] and sweep['source_commit'] == commit and sweep['module_count'] == 169
assert sweep['all_selected_source_hashes_match'] and sweep['errors'] == 0
assert admissions['passed'] and admissions['source_commit'] == commit
assert admissions['base_count'] == 22 and admissions['final_count'] == 21 and not admissions['added']
assert lint['passed'] and not lint['new_failures']
assert reproduction['passed'] and reproduction['commit'] == commit and reproduction['patch_count'] == 4
assert reproduction['reproduced_tree'] == subprocess.check_output(['git','rev-parse',commit+'^{tree}'],cwd=repo,text=True).strip()
for p in ev.rglob('*.gz'):
    with gzip.open(p,'rb') as f:
        while f.read(1024*1024):
            pass
result = dict(source_commit=commit,verified_at_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    source_scope_pass=True,frozen_statement_pass=True,modules=169,compile_errors=0,admissions_removed=['hashAndSign_oneTimeSecure'],
    source_seal_cells=20,all_native_guard_audits_pass=True,closed_rule10_logs_checked=len(index['closed_probe_raw_logs']),
    final_control_probes=22,exactly_one_error_per_sealed_negative=11,stored_constants_audited=176,
    target_axioms=sorted(axioms['target'][0]['axioms']),explicit_foreign_definition_uses=0,
    new_lint_failures=0,patch_count=4,patch_tree_reproduced=True,
    baseline_facade_provenance_limitation=index['baseline_facade_limitation'],passed=True)
(ev/'logs/final-verification.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
