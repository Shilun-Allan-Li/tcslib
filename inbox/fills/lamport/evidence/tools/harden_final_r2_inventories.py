"""Retain original probes and add exact imported-TCSlib-home census guards, no Lean."""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

root, evidence = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
revision = '47ced271090f45918645c842cd358c5079092754'
prep = evidence / 'preparation/final18-r2'
output = prep / 'native-hardening-r1'
assert not output.exists()
output.mkdir()
(output / 'tools').mkdir()
original_queue = (prep / 'queue.json').read_bytes()
(output / 'queue.original.json').write_bytes(original_queue)
queue = json.loads(original_queue)
assert queue['revision'] == revision and queue['count'] == 18
head = subprocess.check_output(['git', '--no-optional-locks', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
assert head == revision
comparison_path = evidence / 'logs/final-sweep-comparison-r2/report.json'
comparison = json.loads(comparison_path.read_text())
assert comparison['status'] == 'PASS' and comparison['expected_modules'] == 177
assert comparison['final_admission_declaration_count'] == 21
audit = json.loads((evidence / 'inputs/final-r2-order-audit.json').read_text())


def source_hashes():
    actual = {}
    for module, expected in audit['source_sha256'].items():
        raw = (root / (module + '.lean')).read_bytes()
        actual[module] = hashlib.sha256(raw).hexdigest()
        assert actual[module] == expected, module
    return actual


before = source_hashes()
guard = '''  let mut exactHomes : Nat := 0
  for imported in env.header.moduleNames do
    if (`TCSlib).isPrefixOf imported then
      unless homes.contains imported.toString do
        throwError "LAMP-INVENTORY unexpected TCSlib home {imported}"
      exactHomes := exactHomes + 1
  unless exactHomes == homes.length do
    throwError "LAMP-INVENTORY exact TCSlib closure count differs"
  logInfo m!"LAMP-CLOSURE-EXACT\\t{target}\\t{exactHomes}"
'''
for record in queue['records']:
    phase = record['phase']
    saved = output / phase
    saved.mkdir()
    source = root / (record['collector_module'] + '.lean')
    original = source.read_bytes()
    assert hashlib.sha256(original).hexdigest() == record['collector_source_sha256']
    assert original == (Path(record['phase_directory']) / 'Inventory.lean').read_bytes()
    (saved / 'Inventory.original.lean').write_bytes(original)
    (saved / 'manifest.original.json').write_bytes(Path(record['manifest']).read_bytes())
    text = original.decode()
    needle = '  let mut rows : Array String := #[]\n'
    assert text.count(needle) == 1
    hardened = text.replace(needle, guard + needle).encode()
    source.write_bytes(hardened)
    (saved / 'Inventory.hardened.lean').write_bytes(hardened)
    record['collector_original_source_sha256'] = record['collector_source_sha256']
    record['collector_source_sha256'] = hashlib.sha256(hardened).hexdigest()
    record['collector_hardened_source'] = str(saved / 'Inventory.hardened.lean')
    record['exact_tcs_import_closure_guard'] = True
after = source_hashes()
assert before == after
versions = {}
for name, path in {
    'prepare_seals_final_r2.py': evidence / 'tools/prepare_seals_final_r2.py',
    'prepare_seals.original.py': prep / 'tools/prepare_seals.py',
    'run_seals.py': evidence / 'tools/run_seals.py',
    'check_helper.py': evidence / 'tools/check_helper.py',
    'lean_host_guard.py': evidence / 'tools/lean_host_guard.py',
    'harden_final_r2_inventories.py': Path(__file__),
}.items():
    raw = path.read_bytes()
    (output / 'tools' / name).write_bytes(raw)
    versions[name] = dict(origin=str(path), snapshot=str(output / 'tools' / name),
                          sha256=hashlib.sha256(raw).hexdigest())
queue['inventory_hardening'] = dict(status='PROBE_ONLY_NATIVE_NOT_RUN',
    timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    no_tcs_source_edits=True, source_sha256_before=before, source_sha256_after=after,
    original_queue_sha256=hashlib.sha256(original_queue).hexdigest(),
    completed_final_sweep_comparison=str(comparison_path),
    completed_final_sweep_comparison_sha256=hashlib.sha256(comparison_path.read_bytes()).hexdigest(),
    tool_versions=versions)
queue['prepare_tool'] = str(output / 'tools/prepare_seals_final_r2.py')
queue['run_seals_tool'] = str(output / 'tools/run_seals.py')
queue['check_helper_tool'] = str(output / 'tools/check_helper.py')
(output / 'queue.json').write_text(json.dumps(queue, indent=2) + '\n')
print(output / 'queue.json')
