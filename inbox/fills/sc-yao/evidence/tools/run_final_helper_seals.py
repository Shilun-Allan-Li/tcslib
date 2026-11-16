#!/usr/bin/env python3
"""Lead-run seals in three output-only trees while locking imported artifacts read-only."""
import datetime
import fcntl
import hashlib
import json
from pathlib import Path
import subprocess

root = Path.cwd()
lock = (root / '.lake/sc-yao-driver.lock').open('a+')
fcntl.flock(lock, fcntl.LOCK_SH | fcntl.LOCK_NB)
manifest_path = Path('evidence/seals/complete-helper-files/final/manifest.json')
manifest = json.loads(manifest_path.read_text())
assert len(manifest) == 272
logdir = Path('evidence/logs/final-helper-seals')
logdir.mkdir(exist_ok=False)
import_tree = root / '.lake/sc-yao-oleans/TCSlib'

def fingerprints():
    return {str(p.relative_to(import_tree)):
            hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(import_tree.rglob('*')) if p.is_file()}

before = fingerprints()
assert len(before) >= 261
(logdir / 'import-artifacts-before.json').write_text(json.dumps(before, indent=2) + '\n')
expected_probe_hashes = {r['probe']: hashlib.sha256(Path(r['probe']).read_bytes()).hexdigest()
                         for r in manifest}
(logdir / 'expected-probe-hashes.json').write_text(
    json.dumps(expected_probe_hashes, indent=2) + '\n')
children = []
records = []
for i in range(3):
    output_root = '.lake/sc-yao-final-seals-' + str(i)
    assert not (root / output_root).exists()
    run = 'final-helper-seals-' + str(i)
    shard = Path('evidence/seals/complete-helper-files') / ('shard-' + str(i) + '.json')
    assert json.loads(shard.read_text()) == manifest[i::3]
    stream = (logdir / ('shard-' + str(i) + '-stdout.log')).open('w')
    process = subprocess.Popen(['python3', '-I', 'evidence/tools/run_probes.py', str(shard),
        run, '--output-root', output_root, '--read-only-import-lock'],
        stdout=stream, stderr=subprocess.STDOUT)
    children.append((process, stream))
    records.append(dict(shard=i, pid=process.pid, run=run, output_tree=output_root,
        import_tree=str(import_tree.parent), started=datetime.datetime.now(
            datetime.timezone.utc).isoformat()))
(logdir / 'processes.json').write_text(json.dumps(records, indent=2) + '\n')
print('STARTED 3 lead seal shards; wrapper cap unchanged; independent output-only trees', flush=True)
for record, (process, stream) in zip(records, children):
    record['exit'] = process.wait()
    record['ended'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    stream.close()
    (logdir / 'processes.json').write_text(json.dumps(records, indent=2) + '\n')
    print('SHARD', record['shard'], 'TERMINAL', record['exit'], flush=True)
after = fingerprints()
(logdir / 'import-artifacts-after.json').write_text(json.dumps(after, indent=2) + '\n')
assert before == after, 'Imported bootstrap artifacts must be unchanged throughout seals'
rows = []
for record in records:
    assert record['exit'] == 0, record
    rows.extend(json.loads(s) for s in (Path('evidence/probe-runs') / record['run'] /
                                      'results.jsonl').read_text().splitlines())
assert len(rows) == len(manifest)
assert {r['probe'] for r in rows} == {r['probe'] for r in manifest}
assert len({r['probe'] for r in rows}) == len(rows)
assert all(r['source_sha256'] == expected_probe_hashes[r['probe']] for r in rows)
failed = [r for r in rows if r['exit'] or r['errors'] or r['generic_errors']
          or not r['fresh_olean']]
summary = dict(checks=len(rows), all_pass=not failed, failures=failed,
    files=len({r['file'] for r in rows}), independent_output_trees=3,
    read_only_import_artifacts=len(before), import_artifacts_unchanged=before == after,
    probe_hashes_match_initial=True, shared_import_locks_in_parent_and_children=True,
    shared_slot_cap=3, runs=[r['run'] for r in records])
Path('evidence/final-helper-seal-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary), flush=True)
assert not failed, failed
