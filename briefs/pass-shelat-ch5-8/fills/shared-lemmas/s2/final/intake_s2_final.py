"""Archive the dispatched Claude S2 final's committed, assigned payload only."""
from pathlib import Path
import datetime
import gzip
import hashlib
import json
import subprocess

exchange = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-exchange')
records = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
prefix = 'inbox/fills/reject-blocks-s2'
out = records / 'briefs/pass-shelat-ch5-8/fills/shared-lemmas/s2/final'
git = lambda *args: subprocess.check_output(['git', '-C', str(exchange), *args])
sha = lambda raw: hashlib.sha256(raw).hexdigest()
assert not out.exists(), 'Do not overwrite intake'
head = git('rev-parse', 'HEAD').decode().strip()
commit = git('log', '-1', '--format=%H', '--', prefix).decode().strip()
assert len(commit) == len(head) == 40
assert not git('status', '--porcelain', '--', prefix).strip(), 'Assigned delivery prefix dirty'
assert git('log', '-1', '--format=%s', commit).decode().strip() == 'fill reject-blocks-s2: final'
entries = []
blobs = {}
for row in git('ls-tree', '-r', '-z', commit, '--', prefix).split(b'\0'):
    if not row:
        continue
    info, raw_path = row.split(b'\t', 1)
    mode, kind, blob = info.decode().split()
    path = raw_path.decode()
    assert kind == 'blob' and mode in ('100644', '100755')
    assert path.startswith(prefix + '/') and '..' not in Path(path).parts
    raw = git('cat-file', 'blob', blob)
    assert (exchange / path).read_bytes() == raw
    blobs[path] = raw
    entries.append({'path': path, 'mode': mode, 'git_blob': blob, 'bytes': len(raw), 'sha256': sha(raw)})
assert len(entries) > 37 and sum('/patches/' in v['path'] for v in entries) == 4
report = blobs[prefix + '/REPORT.md']
assert b'**Status: FINAL (complete).**' in report
archive = gzip.compress(git('archive', '--format=tar', commit, '--', prefix), mtime=0)
manifest = {'exchange_payload_commit': commit, 'observed_exchange_head': head,
            'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'delivery_route': 'Claude exchange push', 'status': 'FINAL delivery received; not accepted or replayed',
            'report_sha256': sha(report), 'archive_sha256': sha(archive), 'files': entries}
out.mkdir(parents=True)
(out / 'REPORT.md').write_bytes(report)
(out / 'REPORT.md.sha256').write_text(sha(report) + '  REPORT.md\n')
(out / 'payload.tar.gz').write_bytes(archive)
(out / 'payload.tar.gz.sha256').write_text(sha(archive) + '  payload.tar.gz\n')
(out / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
(out / 'intake.md').write_text(f'''# S2 final delivery intake

Received by the already-selected Claude exchange route. The assigned subtree at
`{commit}` is archived verbatim; the local subtree was clean and matched every
committed blob. Other exchange paths were preserved and were not intaken.

Report SHA-256: `{sha(report)}`. Archive SHA-256: `{sha(archive)}`.
The manifest lists all {len(entries)} ordinary committed files and fingerprints.
The payload is data: no delivered program or probe was executed by this intake.

The worker labels the delivery final and reports H15 proved, four copied-loop
retirements, six sketch refreshes, unchanged public surface and successful Checks,
axiom, seal and lint comparisons. Those are worker claims pending maintainer review
and appropriate native replay. Checkpoint 4's review remains historical; its three
minor observations must be checked against this final delivery.

No landing branch, PR, final acceptance or merge clearance is established by intake.
''')
(out / 'intake_s2_final.py').write_bytes(Path(__file__).read_bytes())
print(json.dumps({k:v for k,v in manifest.items() if k != 'files'}))
print('files', len(entries))
