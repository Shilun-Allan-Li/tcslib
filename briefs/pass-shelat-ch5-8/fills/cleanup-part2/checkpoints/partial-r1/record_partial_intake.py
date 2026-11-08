"""File the incoming final-PARTIAL delivery verbatim, before resolutions."""
from pathlib import Path
import hashlib
import json
import subprocess

PREP = Path(__file__).resolve().parent
SOURCE = PREP / 'partial-r1'
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
UNIT = MAIN / 'briefs/pass-shelat-ch5-8/fills/cleanup-part2'
DEST = UNIT / 'checkpoints/partial-r1'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-C', str(MAIN), *args], text=True).strip()


def main():
    assert git('branch', '--show-current') == 'cryptography/pass-shelat-ch2-4'
    assert not git('status', '--porcelain')
    git('pull', '--ff-only', 'origin', 'cryptography/pass-shelat-ch2-4')
    assert not git('status', '--porcelain') and not DEST.exists()
    intake = json.loads((SOURCE / 'intake.json').read_text())
    assert intake['delivery_commit'] == '0c4d4f60203021f3a3b93f88eaf7c9085c6ab885'
    assert intake['files'] == 3936 and intake['source_snapshots'] == 221
    assert not intake['payload_checksum_issues'] and not intake['source_missing_owned'] and not intake['source_outside_owned']
    assert sha((SOURCE / 'received.zip').read_bytes()) == intake['archive_sha256']
    assert sha((SOURCE / 'REPORT.md').read_bytes()) == intake['report_sha256']
    DEST.mkdir()
    for name in ['received.zip', 'REPORT.md', 'PAYLOAD-SHA256SUMS', 'files.json', 'intake.json']:
        (DEST / name).write_bytes((SOURCE / name).read_bytes())
    (DEST / 'record_partial_intake.py').write_bytes(Path(__file__).read_bytes())
    (DEST / 'README.md').write_text(f'''# Cleanup final-PARTIAL delivery: immutable intake

Claude pushed `{intake['delivery_commit']}` on exchange/pass-shelat-ch5-8,
under the assigned inbox/fills/cleanup-part2/ subtree. The 30-minute watch detected
it at 2026-11-08T10:56:08Z. The commit is named final; its report explicitly says
FINAL DELIVERY — PARTIAL, not final-complete. No completion is inferred.

The archive is the maintainer's Git archive of that immutable subtree, not a
worker-uploaded ZIP. REPORT.md and PAYLOAD-SHA256SUMS are copied verbatim.
files.json binds every Git blob/mode, size and SHA-256; supplied checksums match
after ordinary ./ normalization. All 221 owned source snapshots are present,
without an outside-owned snapshot. Executable-mode files are retained as data.

- 3,936 files; 49,015,725 raw bytes.
- Archive SHA-256: `{intake['archive_sha256']}`.
- REPORT SHA-256: `{intake['report_sha256']}`.
- Worker claims source head `03ead73ab38e74621800367c072f6fd3f0f70991`,
  thirteen whole patches, 122 changed source paths, 26 provider-only insertions.
- Worker reports 173/509 keys and 152/764 historical rows still open, plus
  further failing declarations, E-API and E-FREEZE. These counts and all native,
  seal/control/census/disposition claims require independent review.

Independent source/freeze, workflow/evidence and API/frontier reviews are underway,
using the snapshot rather than mutable exchange files. No incoming program has
been executed, no source applied, no new external job dispatched, and no ruling
or merge clearance is granted by intake. The CP1 local API follow-up remains a
separate checked local commit; it is not implicitly in this worker payload.

**Not yet clear to merge — final-PARTIAL delivery received; independent review and incomplete work remain.**
''')
    sums = [f'{sha(file.read_bytes())}  {file.relative_to(DEST).as_posix()}'
            for file in sorted(DEST.rglob('*')) if file.is_file()]
    (DEST / 'SHA256SUMS').write_text('\n'.join(sums) + '\n')
    readme = UNIT / 'README.md'
    text = readme.read_text()
    text = text.replace('The single Claude job is active.',
        'Claude has delivered a [final-PARTIAL snapshot](checkpoints/partial-r1/README.md); independent review is underway.')
    text = text.replace('The user requested30-minute checks for the next partial delivery.',
        'The user-requested 30-minute watch detected that delivery at 10:56:08 UTC; the maintainer is now reviewing it.')
    text = text.replace('**Not yet clear to merge — CP1 is intermediate; review, inherited-read repair and final evidence remain.**',
        '**Not yet clear to merge — the final-PARTIAL delivery is under review and inherited-read work remains.**')
    readme.write_text(text)
    dispatch = UNIT / 'dispatch.md'
    text = dispatch.read_text().replace('**Active Claude fill.** Checkpoints0and1 received;',
        '**Claude final-PARTIAL delivery received.** Checkpoints0and1 and delivery `0c4d4f60203021f3a3b93f88eaf7c9085c6ab885` are archived;')
    text = text.replace('**Not yet clear to merge — Claude fill active; CP1 review and the upcoming partial delivery remain.**',
        '**Not yet clear to merge — the final-PARTIAL delivery is received and independent review is underway.**')
    dispatch.write_text(text)
    handoff = MAIN / 'briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md'
    text = handoff.read_text().replace('**Cleanup part2 Claude fill active**,',
        '**Cleanup part2 Claude final-PARTIAL delivered**,')
    old = 'the next partial-delivery watch continues.'
    new = ('the 30-minute watch detected final-PARTIAL delivery '
           '`0c4d4f60203021f3a3b93f88eaf7c9085c6ab885` at 10:56:08 UTC, archived verbatim '
           'under `checkpoints/partial-r1/`. All3,936 raw file/checksum/Git identities and221 source paths '
           'verify. Worker head `03ead73ab38e74621800367c072f6fd3f0f70991` has13 patches and reports '
           '173/509 keys still open with E-API/E-FREEZE. Independent source, evidence and frontier '
           'reviews are underway; no completion, source application or ruling is inferred.')
    assert text.count(old) == 2
    handoff.write_text(text.replace(old, new))
    plan = MAIN / 'PassShelatChapter5-8Plan.md'
    plan.write_text(plan.read_text() + '| 2026-11-08 (PST) | **Expected cleanup partial delivery arrived.** '
        'The 30-minute poll at10:56:08UTC detected Claude exchange `0c4d4f60203021f3a3b93f88eaf7c9085c6ab885` '
        '(commit10:26:00UTC), explicitly FINAL DELIVERY—PARTIAL. Verbatim archive/report/manifests filed before resolutions '
        'under `fills/cleanup-part2/checkpoints/partial-r1/`:3936 files/49,015,725 bytes, '
        'archiveSHA `5e814a991ae91447b6aa18d92e3d65d8c78e8c76cef93769a5f3c37a570393ac`, '
        'REPORTSHA `dca5f8e5961b83b402a6255ff4afd4273a555e3d04a9f1fb391fa15acdb8b57e`. '
        'All raw checksum/Git identities and221-source set verify. Reported source03ead73ab38e74621800367c072f6fd3f0f70991 '
        'has13 patches/122 source paths/26 providers and173 open keys, not completed cleanup. '
        'Source/freeze, evidence and claimed E-API/E-FREEZE frontier reviews started. No incoming program executed, '
        'source applied, external dispatch, ruling or merge clearance at intake. | record |\n')
    git('diff', '--check')
    state = json.loads((PREP / 'watch.json').read_text())
    state['last_delivery'] = intake['delivery_commit']
    state.pop('pending_delivery', None)
    state['expected_delivery_received'] = True
    state['current_phase'] = 'REVIEW_FINAL_PARTIAL_AND_ADVANCE_AUTHORIZED_WORK'
    state['review_snapshot'] = str(SOURCE)
    (PREP / 'watch.json').write_text(json.dumps(state, indent=2) + '\n')
    print(json.dumps({'record_root': str(DEST), 'delivery': intake['delivery_commit'],
                      'status': 'WRITTEN_NOT_COMMITTED', 'source_applied': False}, indent=2))


if __name__ == '__main__':
    main()
