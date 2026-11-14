"""Prepare immutable r3 installer queue/resumable runner; no Lean/source mutation."""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess

evidence = Path('/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence')
root = Path('/private/tmp/tcslib-lamport-01a1d88f/proof')
old_queue = evidence / 'preparation/final18-r2/native-hardening-r1/queue.json'
dest = evidence / 'preparation/final18-r2/cached-installer-r3'
assert not dest.exists()
dest.mkdir()
(dest / 'tools').mkdir()
sha = lambda raw: hashlib.sha256(raw).hexdigest()
old_raw = old_queue.read_bytes()
queue = json.loads(old_raw)
assert subprocess.check_output(['git', '--no-optional-locks', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip() == queue['revision']
audit = json.loads((evidence / 'inputs/final-r2-order-audit.json').read_text())
hashes = {m: sha((root / (m + '.lean')).read_bytes()) for m in audit['source_sha256']}
assert hashes == audit['source_sha256']
(dest / 'queue.original.json').write_bytes(old_raw)
versions = {}
tool_sources = {
    'prepare_seals.py': evidence / 'proposals/cached-module-names-r3/prepare_seals_candidate.py',
    'run_seals.py': Path(queue['run_seals_tool']),
    'check_helper.py': Path(queue['check_helper_tool']),
    'lean_host_guard.py': evidence / 'tools/lean_host_guard.py',
    'run_final18_native_r3.py': evidence / 'proposals/native-runner-resume-r2/run_final18_native_r2.py',
    'prepare_cached_final18_queue.py': Path(__file__),
}
for name, source in tool_sources.items():
    raw = source.read_bytes()
    if name == 'run_final18_native_r3.py':
        text = raw.decode()
        needle = "for item in queue['inventory_hardening']['tool_versions'].values():"
        gate = '''gate = queue.get('activation_gate')
if gate:
    qualification = json.loads(Path(gate['full_planted_qualification_summary']).read_text())
    assert qualification['queue_complete'] and qualification['expected_probes'] == qualification['checked_probes'] == 8
    assert qualification['status_counts'] == {'SOURCE_PASS': 2, 'CONTROL_PASS': 6}
    assert qualification['all_harnesses_and_controls_valid'] and qualification['all_source_seals_pass']
'''
        assert text.count(needle) == 1
        text = text.replace(needle, gate + needle)
        needle = "                   source_hashes_unchanged=True)"
        assert text.count(needle) == 1
        text = text.replace(needle, "                   source_hashes_unchanged=True, native_results_adopted=adopt,\n                   adopted_native_queue=queue.get('adopted_native_queue') if adopt else None)")
        compile(text, str(dest / 'tools' / name), 'exec')
        raw = text.encode()
    target = dest / 'tools' / name
    target.write_bytes(raw)
    versions[name] = dict(origin=str(source), snapshot=str(target), sha256=sha(raw))
first_four = [x['phase'] for x in queue['records'][:4]]
assert first_four == ['FinalR2Planted', 'FinalR2Encoding', 'FinalR2TableCoins', 'FinalR2Averaging']
for index, record in enumerate(queue['records']):
    record['native_status'] = 'ADOPT_SUCCESSFUL_OLD_NATIVE_RESULTS' if index < 4 else 'NOT_RUN'
    record['preparation_tool_version'] = 'original-final-r2' if index < 4 else 'cached-module-names-r3'
    record['collector_tool_version'] = 'original-hardened-r1'
    if index < 4:
        record['adopted_native_seal_attempt'] = str(evidence / 'logs/seals' / (record['phase'].lower() + '-native-r1'))
queue['prepare_tool'] = str(dest / 'tools/prepare_seals.py')
queue['run_seals_tool'] = str(dest / 'tools/run_seals.py')
queue['check_helper_tool'] = str(dest / 'tools/check_helper.py')
queue['driver_tool'] = str(dest / 'tools/run_final18_native_r3.py')
queue['adopted_native_queue'] = dict(path=str(old_queue), sha256=sha(old_raw), phases=first_four,
                                    original_tool_versions=queue['inventory_hardening']['tool_versions'])
queue['installer_r3'] = dict(prepared_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    tool_versions=versions, change='Only cache captured env.header.moduleNames once in each INSTALL/EOF command',
    qualification_status='REQUIRED_BEFORE_ACTIVATION', first_four_adopted_without_recheck=True,
    remaining_phases=len(queue['records']) - 4, no_tcs_source_edits=True,
    collector_cache_status='NOT_ROLLED_OUT_PENDING_SEPARATE_PROPOSAL_AND_NATIVE_COMPARISON')
queue['inventory_hardening']['tool_versions'] = dict(queue['inventory_hardening']['tool_versions'], **versions)
queue['activation_gate'] = dict(full_planted_qualification_summary=str(evidence / 'logs/seals/cache-qualification-r1/summary.json'))
queue['status'] = 'PREPARED_REQUIRES_R3_FULL_QUALIFICATION'
(dest / 'queue.json').write_text(json.dumps(queue, indent=2) + '\n')
command = ['python3', '-I', queue['driver_tool'], '--queue', str(dest / 'queue.json'),
           '--attempt', 'final18-native-r3', '--adopt-through', 'FinalR2Averaging',
           '--pause-file', str(evidence / 'requests/pause-final18-r3')]
(dest / 'activation-command.json').write_text(json.dumps(command, indent=2) + '\n')
(dest / 'README.md').write_text('Prepared source-only. Original stopped manager and all Inventory.lean files are unchanged. '
    'The driver requires complete successful full8 Planted r3 qualification before checking any native module. '
    'It adopts first4 exact old snapshot/collector/seal attempts, reuses first3 immutable scans, and produces missing Averaging scan/phase summary. '
    'Later14 phases use cached r3 seal generation; their collectors remain the original hardened r1 sources pending a separately approved cache overlay. '
    'The phase-boundary pause file is checked before each new phase. All old attempts and tool versions remain retained.\n')
assert hashes == {m: sha((root / (m + '.lean')).read_bytes()) for m in audit['source_sha256']}
print(dest / 'queue.json')
print(json.dumps(dict(first_four_adopted=first_four, remaining=14, source_hashes_unchanged=True)))
