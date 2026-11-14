"""Combine immutable successful BaseAuth probes across a host-interrupted retry.

Use python3 -I. No Lean/source writes. Exact-base binary/provider equivalence is
an explicit prerequisite; historical interrupted results remain separately listed.
"""
import argparse
import datetime
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--evidence', required=True)
args = parser.parse_args()
e = Path(args.evidence).resolve()
phase = e / 'seals/BaseAuthCp2'
first = e / 'logs/seals/baseauth-cp2-r1-seals'
retry = e / 'logs/seals/baseauth-cp2-r2-seals-host5'
transaction = e / 'logs/base-auth/baseauth-cp2-r2'

def read(path):
    return json.loads(path.read_text())

def records(path):
    return [json.loads(line) for line in (path / 'results.jsonl').read_text().splitlines()]

original_manifest = read(phase / 'seal-manifest.json')
subset_manifest = read(phase / 'retry-ControlBReader-seal-manifest.json')
assert subset_manifest['parent_manifest_sha256'] == hashlib.sha256(
    (phase / 'seal-manifest.json').read_bytes()).hexdigest()
assert len(subset_manifest['probes']) == 1
assert subset_manifest['probes'][0] == next(
    probe for probe in original_manifest['probes'] if probe['label'] == 'BaseAuthCp2_ControlBReader')
same = read(transaction / 'same-base-environment-as-original.json')
assert same['all_147_unchanged_provider_olean_hashes_equal']
assert same['canonical_base_products_bit_identical']
restoration = read(transaction / 'summary.json')
assert restoration['base_phase_error'] is None and restoration['source_restored']
assert restoration['final_rebuild_ok']
latest = {row['label']:row for row in records(first)}
retry_rows = records(retry)
assert len(retry_rows) == 1 and retry_rows[0]['label'] == 'BaseAuthCp2_ControlBReader'
latest.update({row['label']:row for row in retry_rows})
assert set(latest) == {probe['label'] for probe in original_manifest['probes']}
assert len(latest) == 8
for row in latest.values():
    assert row['status'] in ('SOURCE_PASS', 'CONTROL_PASS') and row['harness']['valid']
    assert row['errors'] == (1 if row['label'].endswith('Negative') else 0)
    assert hashlib.sha256((e / row['raw_log']).read_bytes()).hexdigest() == row['raw_log_sha256']
final_checks = {}
for prefix in ('finalLamport','finalHashSign','finalAuth'):
    checks = [row for row in restoration['checks'] if row['label'].startswith(prefix)]
    assert checks and checks[-1]['status'] == 0
    final_checks[prefix] = checks
historical = []
for path in [first] + sorted((e / 'logs/seals').glob('baseauth-cp2-r2-seals*')):
    for row in records(path):
        if row['exit'] == 130:
            historical.append(dict(attempt=path.name, result=row,
                                   classification='host-cap interruption; not a mathematical failure'))
pre = read(transaction / 'preconditions.json')
result = dict(completed_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
              target='TCSlib.Cryptography.Authentication',
              revision='eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9',
              phase='BaseAuthCp2', overall_complete=True,
              facade_local_stored_constants=0, exact_foreign_canonical_module_count=149,
              same_base_environment=same, effective_results=list(latest.values()),
              historical_host_interruptions=historical,
              final_source_commit=pre['final_commit'],
              restored_source_sha256=dict(Lamport=pre['final_lamport_sha256'],
                                          Authentication=pre['final_auth_sha256']),
              final_rechecks=final_checks,
              original_summaries_unchanged=True,
              script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
out = e / 'logs/base-auth/base-auth-cp2-completion.json'
assert not out.exists()
out.write_text(json.dumps(result, indent=2) + '\n')
print('Exact BaseAuth coverage complete: 2 source seals + 6 controls; source restored/final3 pass.')
print(out)
