"""File the bounded, checked local API repair as maintainer evidence only."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

PREP = Path(__file__).resolve().parent
CP = PREP / 'cp1'
NATIVE = CP / 'native-api01-r1'
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
UNIT = MAIN / 'briefs/pass-shelat-ch5-8/fills/cleanup-part2'
DEST = UNIT / 'checkpoints/cp1/api01-native-r1'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-C', str(MAIN), *args], text=True).strip()


def main():
    assert git('branch', '--show-current') == 'cryptography/pass-shelat-ch2-4'
    assert not git('status', '--porcelain')
    git('pull', '--ff-only', 'origin', 'cryptography/pass-shelat-ch2-4')
    assert not git('status', '--porcelain') and not DEST.exists()
    result = json.loads((NATIVE / 'RESULT.json').read_text())
    axioms = json.loads((NATIVE / 'API01Axioms.json').read_text())
    repair = json.loads((CP / 'api01-checked-repair.json').read_text())
    attempts = [json.loads(line) for line in (NATIVE / 'attempts.jsonl').read_text().splitlines()]
    assert result['all_passed'] and result['checked_local_modules'] == 101
    assert axioms['passed'] and axioms['standard_only'] and len(axioms['axioms']) == 6
    assert len(attempts) == 102 and all(row['passed'] for row in attempts)
    for row in attempts:
        assert sha((NATIVE / row['log']).read_bytes()) == row['log_sha256']
    assert sha((NATIVE / axioms['log']).read_bytes()) == axioms['log_sha256']
    assert not (NATIVE / 'active-native.json').exists() and not (NATIVE / 'STOP.json').exists()
    assert repair['head'] == '8c047b8bcd3a2793795a02afd6d2d955c80e1806'
    DEST.mkdir()
    members = []
    for root, prefix in [(NATIVE, 'native'), (CP / 'review-api/native-plan', 'plan')]:
        for file in sorted(root.rglob('*')):
            if not file.is_file() or '__pycache__' in file.parts:
                continue
            assert not file.is_symlink()
            members.append((prefix + '/' + file.relative_to(root).as_posix(), file.read_bytes()))
    for name in ['run_native_api01.py', 'run_api01_axioms.py']:
        members.append(('tools/' + name, (PREP / name).read_bytes()))
    archive = DEST / 'native-evidence.zip'
    with zipfile.ZipFile(archive, 'x', zipfile.ZIP_DEFLATED, compresslevel=9) as zipped:
        for name, raw in members:
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 8, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            zipped.writestr(info, raw)
    (DEST / 'manifest.json').write_text(json.dumps({
        'archive_sha256': sha(archive.read_bytes()),
        'files': [{'path': name, 'bytes': len(raw), 'sha256': sha(raw)} for name, raw in members],
    }, indent=2) + '\n')
    for source, name in [(NATIVE / 'RESULT.json', 'RESULT.json'),
                         (NATIVE / 'API01Axioms.json', 'API01Axioms.json'),
                         (CP / 'api01-checked-repair.json', 'repair.json'),
                         (CP / 'api01-checked-repair.patch', 'repair.patch'),
                         (Path(__file__), 'record_api01_native.py')]:
        (DEST / name).write_bytes(source.read_bytes())
    peak = max(row['max_rss_bytes'] or 0 for row in attempts)
    (DEST / 'README.md').write_text(f'''# CP1 API-01: checked local follow-up

**API-01 is corrected on the isolated local review branch**, at
`{repair['head']}`. The immutable CP1 and review-r1 remain unchanged; this is a
separate maintainer follow-up. The worker's continuing source has not incorporated
this local commit by implication.

The patch removes the new whole-machine equality alias and replaces its three
consumers with the existing `NUPPT.output_ofPolyTimeUniform` contract. Four files,
three inserted and ten removed lines; no existing theorem header, algorithm,
bound, assumption or admission changes. Seven preceding worker patches retain
their author attribution. The branch is local only: no source push or PR.

The fresh serial run passed all **101 local prerequisite/consumer modules** plus
a Mathlib cache import probe, using `scripts/lean_check_tree.sh`, one module per
invocation and one native process at a time. A separate final probe printed the
actual axiom sets of the three repaired proofs and three machine API constants.
All six contain only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
All 101 source/object identities and direct prerequisite hashes reconcile.
The run used no TCSlib object copy/reuse and left the old S2 object tree intact.

Preflight: macOS12 logical CPUs /18GiB physical memory, native memory-pressure
query73% free, APFS408,420,340KiB available on clone/scratch/temp volumes;
11 present packages match manifest URL/revision, four doc-only packages absent,
zero empty package oleans. The same-chat pinned package cache was already
populated; all66 direct Mathlib roots and the required external object closure
were present, and the native cache probe passed. No new cache fetch was needed.
Peak recorded per-module RSS was {peak} bytes. Every attempt has an exclusive
log path with START/END/return code/source/prerequisite/log hashes; no attempt
failed or was overwritten. Full preflight and raw evidence are in the ZIP.

The source pins in the native run describe the review head plus the exact repair
diff before it was committed. The final commit changes no checked source byte;
repair.json binds that commit to the patch and run. Native tools are the own
reviewed runners, never incoming checkpoint scripts.

**Limits:** these are ordinary unsealed checks of this bounded API follow-up,
not the entire cleanup affected/downstream/root/Checks replay or fresh full
seal/C3/control/census evidence. Three workflow majors and the ledger minor
remain, alongside unfinished inherited-read repair and the inherited instance
coverage question. This does not accept CP1 or authorize a merge.

**Not yet clear to merge — the local API repair is checked; the remaining partial fill and final evidence are open.**
''')
    addendum = UNIT / 'checkpoints/cp1/log-retention-addendum-r1'
    assert not addendum.exists()
    addendum.mkdir()
    source = CP / 'review-workflow'
    assert sha((source / 'failure-log-addendum.md').read_bytes()) == 'b826874597b0a073442ef84f0d575823b6fdbadb2f9b131229953c244f96b72e'
    for name in ['failure-log-addendum.md', 'failure-log-addendum.json',
                 'check_failure_log_alternates.py']:
        (addendum / name).write_bytes((source / name).read_bytes())
    (addendum / 'README.md').write_text('''# CP1 log-retention qualification

The separate bounded review inspected all 2,589 delivered logs. None contains a
located original diagnostic body for the 30 failed development attempts; all30
retain metadata and two retain console summaries. This establishes absence from
frozen CP1, not permanent unrecoverability outside that payload. Original logs or
session output may still be supplied as a pinned supplement, matched by exact
attempt/source/start; reconstructed reruns must not be called the originals.

This qualifies any broader permanent-loss wording in review-r1 and its initial
maintainer resolutions. Those earlier records remain unchanged. The observed
path overwrite and need for unique future attempt logs remain open W2 findings.
The attached report/JSON/own validator are verbatim; no worker was contacted.

**Not yet clear to merge — the evidence gap is qualified and remains open.**
''')
    addendum_sums = [f'{sha(file.read_bytes())}  {file.name}'
                     for file in sorted(addendum.iterdir()) if file.is_file()]
    (addendum / 'SHA256SUMS').write_text('\n'.join(addendum_sums) + '\n')
    readme = UNIT / 'README.md'
    text = readme.read_text().replace('the isolated API repair awaits native checks.',
        'the [isolated API repair](checkpoints/cp1/api01-native-r1/README.md) passed a fresh101-module native closure and six selected actual-axiom checks. It is committed locally only; three workflow majors and the ledger minor remain.')
    readme.write_text(text)
    handoff = MAIN / 'briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md'
    text = handoff.read_text()
    old = ('a bounded operational-reader repair is uncompiled/uncommitted. No source push/PR. '
           'Fresh serial native checks are planned; the next partial-delivery watch continues.')
    new = ('the bounded operational-reader repair is committed locally at '
           '`8c047b8bcd3a2793795a02afd6d2d955c80e1806` and passed101 fresh serial prerequisite/consumer '
           'module checks plus six actual-axiom checks (standard only), recorded in `checkpoints/cp1/api01-native-r1/`. '
           'API-01 is locally corrected; three workflow majors and the ledger minor remain. No source push/PR; '
           'the next partial-delivery watch continues.')
    assert text.count(old) == 2
    handoff.write_text(text.replace(old, new))
    plan = MAIN / 'PassShelatChapter5-8Plan.md'
    plan.write_text(plan.read_text() + '| 2026-11-08 (PST) | **CP1 API-01 bounded local repair checked.** '
        'Local review head `8c047b8bcd3a2793795a02afd6d2d955c80e1806` removes the new whole-machine alias and uses '
        'the existing output contract in three proofs;4 files, unchanged existing headers/algorithms/admissions. '
        'Fresh empty-tree101-module serial closure + Mathlib import probe pass; all source/object/direct-prerequisite identities reconcile. '
        'Six selected actual axiom sets standard-only, no sorryAx. Exclusive complete per-attempt logs/own runners/plan/preflight archived '
        'in `checkpoints/cp1/api01-native-r1/`; no incoming script executed, no TCS object reuse/copy, old S2 tree untouched. '
        'Local commit only, no source push/PR. Immutable CP1 review stays unchanged;3 workflow majors/ledger minor/inherited reads/final '
        'verification remain. Separate log-retention addendum inspected2589 delivered logs:0/30 original diagnostic bodies, '
        'all30 metadata and2 console summaries; this is payload absence, not permanent unrecoverability outside CP1. '
        'Earlier broad loss wording is qualified, original records unchanged.30-minute upcoming partial-delivery watch continues. | record |\n')
    sums = [f'{sha(file.read_bytes())}  {file.relative_to(DEST).as_posix()}'
            for file in sorted(DEST.rglob('*')) if file.is_file()]
    (DEST / 'SHA256SUMS').write_text('\n'.join(sums) + '\n')
    git('diff', '--check')
    print(json.dumps({'record_root': str(DEST), 'files': len(sums) + 1,
                      'archive_bytes': archive.stat().st_size,
                      'archive_sha256': sha(archive.read_bytes()),
                      'status': 'WRITTEN_NOT_COMMITTED'}, indent=2))


if __name__ == '__main__':
    main()
