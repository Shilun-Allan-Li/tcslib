"""Archive bounded maintainer CP1 reviews as D-0 records; no Lean mutation."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

PREP = Path(__file__).resolve().parent
CP = PREP / 'cp1'
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
UNIT = MAIN / 'briefs/pass-shelat-ch5-8/fills/cleanup-part2'
DEST = UNIT / 'checkpoints/cp1/review-r1'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-C', str(MAIN), *args], text=True).strip()


def main():
    assert git('branch', '--show-current') == 'cryptography/pass-shelat-ch2-4'
    assert not git('status', '--porcelain')
    before = git('rev-parse', 'HEAD')
    git('pull', '--ff-only', 'origin', 'cryptography/pass-shelat-ch2-4')
    assert not git('status', '--porcelain')
    assert not DEST.exists()
    DEST.mkdir()
    reports = [
        ('review-api', '791a0a37b197370762e02093c82aa98b47a2c4b9043abd4f83ce037659869917'),
        ('review-source-scope', '1068131da626d3a1e2249230ffb354d10596ac656e158467d720a60b54990ece'),
        ('review-workflow', '42cee1bd5caae6d24779af76ca563838125c8f27843d2202ef0d7d0ba2fc2e18'),
    ]
    rows = []
    for name, expected in reports:
        source = CP / name
        assert sha((source / 'report.md').read_bytes()) == expected, name
        raw_files = []
        for file in sorted(source.rglob('*')):
            if not file.is_file() or '__pycache__' in file.parts:
                continue
            rel = file.relative_to(source)
            if 'native-plan' in rel.parts:
                continue
            assert not file.is_symlink()
            raw = file.read_bytes()
            raw_files.append((rel.as_posix(), raw))
        archive = DEST / (name + '.zip')
        with zipfile.ZipFile(archive, 'x', zipfile.ZIP_DEFLATED, compresslevel=9) as zipped:
            for rel, raw in raw_files:
                info = zipfile.ZipInfo(rel, date_time=(2026, 11, 8, 0, 0, 0))
                info.external_attr = 0o100644 << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                zipped.writestr(info, raw)
        (DEST / (name + '.md')).write_bytes((source / 'report.md').read_bytes())
        (DEST / (name + '.json')).write_bytes((source / 'report.json').read_bytes())
        rows.append({'review': name, 'report_sha256': expected,
                     'archive_sha256': sha(archive.read_bytes()),
                     'files': [{'path': rel, 'bytes': len(raw), 'sha256': sha(raw)}
                               for rel, raw in raw_files]})
    for name in ['local-review-branch.json', 'api01-local-repair.json',
                 'api01-combined-applied-uncompiled.patch']:
        (DEST / name).write_bytes((CP / name).read_bytes())
    (DEST / 'resolutions.md').write_bytes((CP / 'resolutions-draft.md').read_bytes())
    (DEST / 'record_cp1_reviews.py').write_bytes(Path(__file__).read_bytes())
    (DEST / 'reviews-manifest.json').write_text(json.dumps({
        'cp1_delivery': '8b133945c3ba4aa7abb3b896bec38441535959b2',
        'reviews': rows,
        'duplicate_source_api_major_counted_once': True,
        'unique_findings': {'blockers': 0, 'majors': 4, 'minors': 1},
        'no_native_result_reproduced': True,
        'no_received_program_executed': True,
    }, indent=2) + '\n')
    (DEST / 'README.md').write_text('''# Cleanup CP1: independent review r1

Three verbatim bounded maintainer reviews and their full own validation artifacts
are preserved here. Each ZIP contains the original review files, including the
source review's complete final lexical declaration maps. The received delivery
remains in the parent directory, unchanged. reviews-manifest.json binds reports,
archives and every archived member. SHA256SUMS binds this complete review record.

Unique findings: **0 blockers, 4 majors, 1 minor**. The source/API reviews identify
the same machine-reader major; it is counted once. See resolutions.md for precise
open dispositions, the historical failed-log gap and inherited instance-filter
coverage limit. None of these reviews ran Lean or executed incoming tools.

The source was replayed with worker authorship in a suitable existing worktree on
cryptography/pass-shelat-cleanup-part2-review. The local four-file repair is
uncompiled/uncommitted at this record. No source branch was pushed and no PR or
merge clearance is implied. Gate06's audited source remains frozen.

**Not yet clear to merge — CP1 is partial; four review majors and final verification remain open.**
''')
    parent_readme = UNIT / 'checkpoints/cp1/README.md'
    text = parent_readme.read_text()
    text = text.replace('Reviews follow separately.',
        'Independent bounded reviews are now in [review-r1](review-r1/README.md).')
    text = text.replace('**Not yet clear to merge — immutable delivery intake only; independent reviews remain.**',
        '**Not yet clear to merge — CP1 is partial; independent review has four unique majors and one minor.**')
    parent_readme.write_text(text)
    readme = UNIT / 'README.md'
    text = readme.read_text().replace(
        'are received, with independent CP1 reviews underway.',
        'are received. [Independent CP1 review](checkpoints/cp1/review-r1/README.md) records four unique majors and one minor; the isolated API repair awaits native checks.')
    readme.write_text(text)
    dispatch = UNIT / 'dispatch.md'
    text = dispatch.read_text()
    text = text.replace('**Ready to dispatch — cleanup part2 to Claude, with fresh checkpoint 0 bootstrap validation required.**',
        '**Not yet clear to merge — Claude fill active; CP1 review and the upcoming partial delivery remain.**')
    dispatch.write_text(text)
    handoff = MAIN / 'briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md'
    text = handoff.read_text()
    old = 'independent source/API/workflow reviews are underway.'
    new = ('independent source/API/workflow reviews are recorded in `checkpoints/cp1/review-r1/`: '
           'four unique majors (whole-machine alias, two extra seal omissions, 30 overwritten '
           'failed logs, truncated/penultimate-pin maps) and one ledger/count minor. Source '
           'replay/freeze/admission checks pass within stated lexical limits. The inherited '
           'instance-filter coverage limit is recorded separately. Seven patches are applied '
           'with worker attribution on local `cryptography/pass-shelat-cleanup-part2-review`; '
           'a bounded operational-reader repair is uncompiled/uncommitted. No source push/PR. '
           'Fresh serial native checks are planned; the next partial-delivery watch continues.')
    assert text.count(old) == 2
    handoff.write_text(text.replace(old, new))
    plan = MAIN / 'PassShelatChapter5-8Plan.md'
    plan.write_text(plan.read_text() + '| 2026-11-08 (PST) | **Cleanup CP1 independent bounded review filed.** '
        'Three verbatim reports/own validators/full lexical maps archived at `fills/cleanup-part2/checkpoints/cp1/review-r1/`; '
        '0 blockers / 4 unique majors / 1 minor (source/API alias finding counted once). Seven patches reproduce221 snapshots; '
        '113 authorized paths, existing provider declarations and20 admitted blocks preserved. Open: operational machine-reader shape, '
        'two extra notation-helper seal omissions,30 overwritten failed-attempt logs, truncated/penultimate-pin surface maps, '
        '509-key/764-row ledger and count partition. Inherited instance filtering is a separate method coverage limit, not a new CP1 deviation. '
        'Worker authorship preserved in isolated local review branch; bounded four-file API repair uncompiled/uncommitted, '
        'no source push or PR. Planned101-module fresh native closure is distinct from worker evidence. User30-minute watch continues; '
        'no worker contact/new dispatch/ruling/merge clearance. | record |\n')
    manifest = []
    for file in sorted(DEST.rglob('*')):
        if file.is_file():
            manifest.append(f'{sha(file.read_bytes())}  {file.relative_to(DEST).as_posix()}')
    (DEST / 'SHA256SUMS').write_text('\n'.join(manifest) + '\n')
    git('diff', '--check')
    receipt = {'main_before': before, 'main_after_pull': git('rev-parse', 'HEAD'),
               'record_root': str(DEST), 'reviews': rows,
               'status': 'WRITTEN_NOT_YET_COMMITTED', 'lean_changes': False}
    (PREP / 'cp1-review-records.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k:v for k,v in receipt.items() if k != 'reviews'}, indent=2))


if __name__ == '__main__':
    main()
