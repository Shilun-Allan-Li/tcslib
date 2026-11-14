"""Prepare a fresh queue adding append-only actual-generator provenance, no Lean."""
import datetime
import hashlib
import json
from pathlib import Path

evidence = Path('/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence')
source = evidence / 'preparation/final18-r2/cached-installer-r3'
dest = evidence / 'preparation/final18-r2/cached-installer-r3-provenance-r1'
assert not dest.exists()
dest.mkdir()
(dest / 'tools').mkdir()
sha = lambda raw: hashlib.sha256(raw).hexdigest()
raw_queue = (source / 'queue.json').read_bytes()
queue = json.loads(raw_queue)
(dest / 'queue.original.json').write_bytes(raw_queue)
old_versions = queue['installer_r3']['tool_versions']
versions = {}
for old in sorted((source / 'tools').iterdir()):
    raw = old.read_bytes()
    if old.name == 'run_final18_native_r3.py':
        text = raw.decode()
        function = '''def append_generator_provenance(attempt, generator):
    raw = generator.read_bytes()
    copied = attempt / 'actual_prepare_seals.py'
    if copied.exists():
        assert copied.read_bytes() == raw, 'existing actual-generator copy differs'
    else:
        copied.write_bytes(raw)
    incidental = attempt / 'prepare_seals.py'
    manifest = attempt / 'seal-manifest.json'
    record = dict(actual_generator_path=str(generator), actual_generator_sha256=sha(raw),
                  actual_generator_copy='actual_prepare_seals.py',
                  native_attempt_manifest_sha256=sha(manifest.read_bytes()),
                  annotating_driver_path=str(Path(__file__).resolve()),
                  annotating_driver_sha256=sha(Path(__file__).read_bytes()),
                  automatic_copy_present=incidental.exists())
    if incidental.exists():
        copied_sha = sha(incidental.read_bytes())
        record['automatic_copy_sha256'] = copied_sha
        record['automatic_copy_role'] = 'ACTUAL_SOURCE_GENERATOR' if copied_sha == sha(raw) else 'INCIDENTAL_REFERENCE_NOT_SOURCE_GENERATOR'
    provenance = attempt / 'actual-generator-provenance.json'
    if provenance.exists():
        previous = json.loads(provenance.read_text())
        assert previous['actual_generator_sha256'] == record['actual_generator_sha256']
        assert previous['native_attempt_manifest_sha256'] == record['native_attempt_manifest_sha256']
    else:
        write(provenance, record)


'''
        needle = 'def seals(record, folder, adopt=False):\n'
        assert text.count(needle) == 1
        text = text.replace(needle, function + needle)
        needle = "    phase_dir = Path(record['phase_directory'])\n    manifest_path = phase_dir / 'seal-manifest.json'"
        assert text.count(needle) == 1
        text = text.replace(needle, "    phase_dir = Path(record['phase_directory'])\n    generator_queue = json.loads(Path(queue['adopted_native_queue']['path']).read_text()) if adopt else queue\n    generator = Path(generator_queue['prepare_tool'])\n    manifest_path = phase_dir / 'seal-manifest.json'")
        needle = "        attempt = evidence / 'logs/seals' / name\n        actual = rows(attempt / 'results.jsonl')"
        assert text.count(needle) == 1
        text = text.replace(needle, "        attempt = evidence / 'logs/seals' / name\n        append_generator_provenance(attempt, generator)\n        actual = rows(attempt / 'results.jsonl')")
        needle = "    qualification = json.loads(Path(gate['full_planted_qualification_summary']).read_text())"
        assert text.count(needle) == 1
        text = text.replace(needle, "    qualification_raw = Path(gate['full_planted_qualification_summary']).read_bytes()\n    assert sha(qualification_raw) == gate['full_planted_qualification_summary_sha256']\n    qualification = json.loads(qualification_raw)")
        compile(text, str(dest / 'tools' / old.name), 'exec')
        raw = text.encode()
    target = dest / 'tools' / old.name
    target.write_bytes(raw)
    versions[old.name] = dict(origin=str(old), snapshot=str(target), sha256=sha(raw))
tool = dest / 'tools' / Path(__file__).name
tool.write_bytes(Path(__file__).read_bytes())
versions[tool.name] = dict(origin=str(Path(__file__)), snapshot=str(tool), sha256=sha(tool.read_bytes()))
queue['prepare_tool'] = str(dest / 'tools/prepare_seals.py')
queue['run_seals_tool'] = str(dest / 'tools/run_seals.py')
queue['check_helper_tool'] = str(dest / 'tools/check_helper.py')
queue['driver_tool'] = str(dest / 'tools/run_final18_native_r3.py')
gate = Path(queue['activation_gate']['full_planted_qualification_summary'])
queue['activation_gate']['full_planted_qualification_summary_sha256'] = sha(gate.read_bytes())
queue['installer_r3']['original_tool_versions'] = old_versions
queue['installer_r3']['tool_versions'] = versions
queue['installer_r3']['provenance_overlay'] = dict(created_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    original_queue=str(source / 'queue.json'), original_queue_sha256=sha(raw_queue),
    append_only_actual_generator_copy_per_attempt=True, source_files_unchanged=True)
queue['inventory_hardening']['tool_versions'] = dict(queue['inventory_hardening']['tool_versions'], **versions)
(dest / 'queue.json').write_text(json.dumps(queue, indent=2) + '\n')
command = ['python3', '-I', queue['driver_tool'], '--queue', str(dest / 'queue.json'),
           '--attempt', 'final18-native-r3', '--adopt-through', 'FinalR2Averaging',
           '--pause-file', str(evidence / 'requests/pause-final18-r3')]
(dest / 'activation-command.json').write_text(json.dumps(command, indent=2) + '\n')
(dest / 'README.md').write_text('Fresh source-only provenance overlay; no native checks or collector/source edits. '
    'Before reading each completed native attempt, driver appends actual_prepare_seals.py and actual-generator-provenance.json. '
    'Adopted first4 select actual old e5217 generator; remaining14 select qualified cached35d744 generator. '
    'Existing prepare_seals.py copies are identified by SHA as actual or incidental reference, never overwritten. '
    'All earlier queue/tool snapshots remain immutable. Cached collector rollout is still pending separately.\n')
print(dest / 'queue.json')
