"""Roll out qualified pure moduleNames caching to remaining14 collector probes."""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess

evidence = Path('/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence')
root = Path('/private/tmp/tcslib-lamport-01a1d88f/proof')
source = evidence / 'preparation/final18-r2/cached-installer-r3-provenance-r1'
dest = evidence / 'preparation/final18-r2/cached-collectors-r3'
assert not dest.exists()
dest.mkdir()
(dest / 'tools').mkdir()
sha = lambda raw: hashlib.sha256(raw).hexdigest()
raw_queue = (source / 'queue.json').read_bytes()
queue = json.loads(raw_queue)
(dest / 'queue.original.json').write_bytes(raw_queue)
audit = json.loads((evidence / 'inputs/final-r2-order-audit.json').read_text())
def frozen():
    assert subprocess.check_output(['git', '--no-optional-locks', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip() == queue['revision']
    actual = {m: sha((root / (m + '.lean')).read_bytes()) for m in audit['source_sha256']}
    assert actual == audit['source_sha256']
    return actual
before = frozen()
qualification = evidence / 'proposals/cached-collector-planted-r1/native-comparison.json'
comparison = json.loads(qualification.read_text())
assert comparison['all_marker_rows_byte_exact'] and comparison['all_marker_multisets_equal']
assert comparison['old_counts'] == comparison['new_counts'] == {'LAMP-CATALOG':9103,'LAMP-AXIOMS':67,'LAMP-CLOSURE-EXACT':1,'LAMP-INVENTORY-END':1}
proposal = evidence / 'proposals/cached-collector-planted-r1'
for name in ('Inventory.original.lean','Inventory.cached.lean','native-comparison.json','metadata.json','proposal.patch','compare_collector_logs.py'):
    (dest / ('qualification-' + name)).write_bytes((proposal / name).read_bytes())
updates = []
for index, record in enumerate(queue['records']):
    if index < 4:
        continue
    phase = record['phase']
    saved = dest / phase
    saved.mkdir()
    native_source = root / (record['collector_module'] + '.lean')
    old = native_source.read_bytes()
    assert sha(old) == record['collector_source_sha256']
    text = old.decode()
    assert text.count('  let env ← getEnv\n') == 1
    assert text.count('env.header.moduleNames') == 4
    cached_text = text.replace('env.header.moduleNames','moduleNames').replace('  let env ← getEnv\n','  let env ← getEnv\n  let moduleNames := env.header.moduleNames\n')
    assert cached_text.count('env.header.moduleNames') == 1
    reversed_text = cached_text.replace('  let moduleNames := env.header.moduleNames\n','').replace('moduleNames','env.header.moduleNames')
    assert reversed_text == text, phase
    cached = cached_text.encode()
    original_path = evidence / 'preparation/final18-r2/native-hardening-r1' / phase / 'Inventory.original.lean'
    original = original_path.read_bytes()
    assert sha(original) == record['collector_original_source_sha256']
    (saved / 'Inventory.original.lean').write_bytes(original)
    (saved / 'Inventory.hardened.lean').write_bytes(old)
    (saved / 'Inventory.cached.lean').write_bytes(cached)
    preparation_raw = Path(record['manifest']).read_bytes()
    (saved / 'manifest.original.json').write_bytes(preparation_raw)
    preparation = json.loads(preparation_raw)
    preparation['inventory_sha256'] = sha(cached)
    preparation['native_collector_overlay'] = dict(original_sha256=sha(original), hardened_sha256=sha(old), cached_sha256=sha(cached),
        change='Cache captured env.header.moduleNames once and reuse its exact array in all4 prior reads',
        qualification=str(qualification), qualification_sha256=sha(qualification.read_bytes()))
    (saved / 'manifest.cached.json').write_text(json.dumps(preparation,indent=2)+'\n')
    record['collector_hardened_source_sha256'] = sha(old)
    record['collector_source_sha256'] = sha(cached)
    record['collector_cached_source'] = str(saved / 'Inventory.cached.lean')
    record['collector_cached_manifest'] = str(saved / 'manifest.cached.json')
    record['collector_tool_version'] = 'qualified-pure-moduleNames-cache-r3'
    record['collector_cache_generator'] = str(dest / 'tools/prepare_cached_collectors_queue.py')
    native_source.write_bytes(cached)
    updates.append(dict(phase=phase, original_sha256=sha(original), hardened_sha256=sha(old), cached_sha256=sha(cached),
                        live_probe=str(native_source), snapshot_imports_unchanged=True))
assert len(updates) == 14
versions = {}
for old in sorted((source / 'tools').iterdir()):
    raw = old.read_bytes()
    if old.name == 'run_final18_native_r3.py':
        text = raw.decode()
        needle = "    assert qualification['all_harnesses_and_controls_valid'] and qualification['all_source_seals_pass']\n"
        assert text.count(needle) == 1
        extra = '''    collector_raw = Path(gate['cached_collector_comparison']).read_bytes()
    assert sha(collector_raw) == gate['cached_collector_comparison_sha256']
    collector_qualification = json.loads(collector_raw)
    assert collector_qualification['all_marker_rows_byte_exact'] and collector_qualification['all_marker_multisets_equal']
    assert collector_qualification['old_counts'] == collector_qualification['new_counts'] == {'LAMP-CATALOG':9103,'LAMP-AXIOMS':67,'LAMP-CLOSURE-EXACT':1,'LAMP-INVENTORY-END':1}
'''
        text = text.replace(needle,needle+extra)
        compile(text,str(dest / 'tools' / old.name),'exec')
        raw = text.encode()
    target = dest / 'tools' / old.name
    target.write_bytes(raw)
    versions[old.name] = dict(origin=str(old), snapshot=str(target), sha256=sha(raw))
target = dest / 'tools' / Path(__file__).name
target.write_bytes(Path(__file__).read_bytes())
versions[target.name] = dict(origin=str(Path(__file__)),snapshot=str(target),sha256=sha(target.read_bytes()))
queue['prepare_tool'] = str(dest / 'tools/prepare_seals.py')
queue['run_seals_tool'] = str(dest / 'tools/run_seals.py')
queue['check_helper_tool'] = str(dest / 'tools/check_helper.py')
queue['driver_tool'] = str(dest / 'tools/run_final18_native_r3.py')
queue['activation_gate']['cached_collector_comparison'] = str(qualification)
queue['activation_gate']['cached_collector_comparison_sha256'] = sha(qualification.read_bytes())
queue['installer_r3']['previous_tool_versions'] = queue['installer_r3']['tool_versions']
queue['installer_r3']['tool_versions'] = versions
queue['installer_r3']['collector_cache_status'] = 'QUALIFIED_REMAINING14_PROBES_CACHED'
queue['inventory_hardening']['tool_versions'] = dict(queue['inventory_hardening']['tool_versions'],**versions)
queue['collector_cache_overlay'] = dict(created_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    original_queue=str(source / 'queue.json'), original_queue_sha256=sha(raw_queue), updates=updates,
    source_sha256_before=before, source_sha256_after=frozen(), no_tcs_source_edits=True,
    first_four_collectors_unchanged=True, qualification_comparison=str(qualification), qualification_sha256=sha(qualification.read_bytes()))
queue['status'] = 'QUALIFIED_NATIVE_READY_FIRST4_ADOPT_REMAINING14_CACHED'
(dest / 'queue.json').write_text(json.dumps(queue,indent=2)+'\n')
command = ['python3','-I',queue['driver_tool'],'--queue',str(dest / 'queue.json'),'--attempt','final18-native-r3',
           '--adopt-through','FinalR2Averaging','--pause-file',str(evidence / 'requests/pause-final18-r3')]
(dest / 'activation-command.json').write_text(json.dumps(command,indent=2)+'\n')
(dest / 'README.md').write_text('Qualified source-only rollout of pure moduleNames caching to remaining14 collector probes. '
    'Preserves issued original, exact-closure-hardened, and cached sources plus manifests and every old queue/tool version. '
    'First4 original native collectors remain unchanged and are adopted with exact original generator provenance. '
    'Activation gates pin full8 sealing qualification and byte-identical complete Planted collector comparison. '
    'No TCSlib source or snapshot import changed; only owned temporary evidence collector probes changed.\n')
print(dest / 'queue.json')
print(json.dumps(dict(cached_collectors=len(updates), first_four_unchanged=True, source_hashes_unchanged=True)))
