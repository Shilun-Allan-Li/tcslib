"""Independently audit each completed singleton control's exact native guards."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--out', required=True, type=Path)
args = p.parse_args()
here = Path(__file__).resolve().parent
plan = [r for r in json.loads((args.out / 'controls-plan.json').read_text()) if 'module' in r]
results = [json.loads(line) for line in (args.out / 'results.jsonl').read_text().splitlines()]
by_module = {r['module']: r for r in results if r.get('expected_error_count') is not None}
audits = []
for control in plan:
    if control['module'] not in by_module:
        raise RuntimeError('control not completed: ' + control['module'])
    result = by_module[control['module']]
    if not result['expectation_passed'] or result['source_sha256'] != control['source_sha256']:
        raise RuntimeError('control source/expectation differs')
    if not control['sealed']:
        audits.append({'module': control['module'], 'label': result['label'], 'unsealed_passed': True})
        continue
    owner_path = args.out / ('seal-' + control['variant']) / (control['request_record'] + '.json')
    owner = json.loads(owner_path.read_text())
    rows = [r for r in owner['rows'] if r['spelling'] in control['request_names']]
    if len(rows) != control['requested'] or len(rows) != 1:
        raise RuntimeError('singleton request scope differs')
    request = {'label': Path(control['module']).name, 'rows': rows, 'requested': 1,
          'owner_request_record': str(owner_path), 'owner_record_sha256': hashlib.sha256(owner_path.read_bytes()).hexdigest(),
          'control_module': control['module'], 'control_source_sha256': control['source_sha256']}
    request_path = args.out / 'control-requests' / (Path(control['module']).name + '.json')
    request_path.parent.mkdir(exist_ok=True)
    request_path.write_text(json.dumps(request, indent=2) + '\n')
    audit_path = args.out / (result['label'] + '.guards.json')
    subprocess.run([sys.executable, '-I', str(here / 'verify_guards.py'), '--record', str(request_path),
            '--log', result['raw_log'], '--out', str(audit_path)], check=True)
    audits.append({'module': control['module'], 'label': result['label'], 'sealed_negative_errors': 1,
         'negative_exact_line_checked': control['negative_start_line'], 'reader_positive_errors': 0,
         'full_singleton_guard_audit': str(audit_path)})
summary = {'control_probes': len(audits), 'unsealed': sum('unsealed_passed' in r for r in audits),
           'sealed_negatives_each_exactly_one_error': sum('sealed_negative_errors' in r for r in audits),
           'all_expectations_and_native_guard_coverage_passed': True, 'audits': audits}
(args.out / 'control-audit-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: v for k, v in summary.items() if k != 'audits'}))
