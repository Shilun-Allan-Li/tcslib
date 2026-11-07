"""Run the prepared Gate06 controls serially; reject harness/setup errors.

Usage: python3 -I run_controls_v3.py <evidence-rule10-dir>
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

r, e = Path.cwd(), Path(sys.argv[1]).resolve()
m = json.loads((e / 'controls-retry-v3-manifest.json').read_text())
assert m['status'] == 'PREPARED_NOT_RUN' and m['root'] == str(r)
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip() == m['library_verification']['head']
out = e / 'control-runs-v3'
out.mkdir(exist_ok=True)
(out / 'run_controls_v3.py').write_bytes(Path(__file__).read_bytes())
assert not (out / 'summary.json').exists()
records = []
for p in m['probes']:
    label = p['label']
    raw = Path(p['probe_path']).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == p['source_sha256']
    assert raw == Path(p['saved_source']).read_bytes()
    result_path = out / (label + '.json')
    if not result_path.exists():
        subprocess.run(['python3', '-I', str(r / '.lake/ps-maintainer/gate06/check_probe_v2.py'),
                        str(out), p['probe_module'], label], check=False)
    result = json.loads(result_path.read_text())
    assert result['source_sha256'] == p['source_sha256'] and result['source_unchanged']
    text = (out / (label + '.log')).read_text()
    errors = [int(n) for n in re.findall(r'\.lean:(\d+):\d+: error(?:\([^\n)]*\))?:', text)]
    expected_errors = p['expected_error_diagnostics']
    assert len(errors) == expected_errors, (label, 'error count', errors)
    if expected_errors:
        assert result['rc'] != 0 and not result['fresh_nonempty_object']
        assert len(errors) == 1 and errors[0] in p['proof_region']['rfl_lines'], (label, 'not sole proof error', errors)
    else:
        assert result['rc'] == 0 and result['fresh_nonempty_object'] and not errors, label
    before = re.findall(r'G06-CONTROL-CATALOG label=' + re.escape(label) + r' phase=before requested=(\d+) verified=(\d+) readers=(\d+)', text)
    assert before == [(str(m['requested_count']), str(m['requested_count']), '3')], (label, before)
    if p['full_closure_sealed']:
        installed = re.findall(r'G06-SEAL label=' + re.escape(label) + r' requested=(\d+) active=(\d+) already_irreducible=(\d+) verified=(\d+)', text)
        expected = (str(m['requested_count']), str(m['collector_active_candidate_count']),
                    str(m['collector_irreducible_count']), str(m['requested_count']))
        assert installed == [expected], (label, installed, expected)
        end = re.findall(r'G06-SEAL-END label=' + re.escape(label) + r' requested=(\d+) verified=(\d+)', text)
        assert end == [(str(m['requested_count']), str(m['requested_count']))], (label, end)
    else:
        after = re.findall(r'G06-CONTROL-CATALOG label=' + re.escape(label) + r' phase=after requested=(\d+) verified=(\d+) readers=(\d+)', text)
        assert after == before, (label, after)
    assert ('G06-CONTROL-BODY-BEGIN ' + label) in text and ('G06-CONTROL-BODY-END ' + label) in text
    record = {**result, 'case': p['case'], 'mode': p['mode'], 'valid_harness': True,
              'expected_outcome': True, 'proof_error_lines': errors,
              'anonymous_only': p.get('anonymous_only', False)}
    records.append(record)
    (out / 'progress.json').write_text(json.dumps(records, indent=2) + '\n')
    print('CONTROL VERIFIED ' + label, flush=True)
assert len(records) == m['expected_totals']['probes'] == 3
summary = {'head': m['library_verification']['head'], 'audited_full_closure': m['audited_module'],
           'requested': m['requested_count'], 'active': m['collector_active_candidate_count'],
           'already_irreducible': m['collector_irreducible_count'], 'controls': records,
           'unsealed_negative_passes': 1, 'sealed_negative_failures': 1,
           'sealed_positive_passes': 1, 'harness_error_diagnostics': 0,
           'anonymous_sensitivity_verified': True, 'matcher_sensitivity_verified_in_this_retry': False, 'earlier_eleven_controls_retained': True,
           'published_readers_verified': True,
           'limit': 'Sensitivity checks for this actual full closure; this is not a library seal pass.'}
(out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print('DONE: constant-AST anonymous negative pair and sealed published-reader control verified', flush=True)
