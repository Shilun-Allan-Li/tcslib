"""File the unrun corrected request plan and concrete provider proposals."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

PREP = Path(__file__).resolve().parent
PART = PREP / 'partial-r1'
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
UNIT = MAIN / 'briefs/pass-shelat-ch5-8/fills/cleanup-part2'
DEST = UNIT / 'checkpoints/partial-r1/corrected-seal-plan-r1'
PROPOSALS = UNIT / 'checkpoints/partial-r1/provider-proposals-r1'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-C', str(MAIN), *args], text=True).strip()


def sums(root):
    rows = [f'{sha(file.read_bytes())}  {file.relative_to(root).as_posix()}'
            for file in sorted(root.rglob('*')) if file.is_file()]
    (root / 'SHA256SUMS').write_text('\n'.join(rows) + '\n')


def main():
    assert git('branch', '--show-current') == 'cryptography/pass-shelat-ch2-4'
    assert not git('status', '--porcelain')
    git('pull', '--ff-only', 'origin', 'cryptography/pass-shelat-ch2-4')
    assert not git('status', '--porcelain') and not DEST.exists() and not PROPOSALS.exists()
    source = PART / 'corrected-seal-plan'
    assert sha((source / 'metadata-manifest.json').read_bytes()) == '17e8a5c776d3ca6736a1d0d773cac656f138ddb5d3f45d2c9eca96143571e8ab'
    assert sha((source / 'README.md').read_bytes()) == '21d8e190891bf7b6778a1a5d40106a6e612ed09fa042824746799170787e7047'
    DEST.mkdir()
    members = [(file.relative_to(source).as_posix(), file.read_bytes())
               for file in sorted(source.rglob('*')) if file.is_file() and '__pycache__' not in file.parts]
    archive = DEST / 'request-plan.zip'
    with zipfile.ZipFile(archive, 'x', zipfile.ZIP_DEFLATED, compresslevel=9) as zipped:
        for name, raw in members:
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 8, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            zipped.writestr(info, raw)
    (DEST / 'archive-manifest.json').write_text(json.dumps({
        'archive_sha256': sha(archive.read_bytes()),
        'files': [{'path': name, 'bytes': len(raw), 'sha256': sha(raw)} for name, raw in members],
    }, indent=2) + '\n')
    for name in ['README.md', 'metadata-manifest.json', 'summary.json']:
        (DEST / name).write_bytes((source / name).read_bytes())
    (DEST / 'record_corrected_plan.py').write_bytes(Path(__file__).read_bytes())
    sums(DEST)
    PROPOSALS.mkdir()
    for file in sorted((PART / 'provider-proof-proposals').iterdir()):
        assert file.is_file() and not file.is_symlink()
        (PROPOSALS / file.name).write_bytes(file.read_bytes())
    (PROPOSALS / 'README.md').write_text('''# Three concrete provider-proof proposals

These standalone patches change only the proofs of Complexity.polyTimeComputable_id,
Complexity.PolyTimeComputable.output_length_le and Complexity.PolyTimeComputable.comp
in ClassNP/PolyTime. They use the existing FinTM.computesFunInTime_iff contract.
Every public header, witness, coefficient/degree, data definition, algorithm,
import and admission remains unchanged. The individual source/result hashes and
boundary notes accompany each patch.

They are **unapplied and uncompiled proposals**, not part of the worker's payload
or the eight current local consumer/API edits. The existing worker PROVIDER_ONLY
restriction remains: issued-r1/public-exceptions.md X12 freezes original provider
proofs. A continuation scope ruling is needed before giving a worker permission
to make these edits; no such ruling is inferred from the patches.

The three examples make the scope choice concrete. Any broader permission for
witnessed provider Rule10 proof repairs must still preserve all public statements,
costs, algorithms and admissions, forbid unrelated refactors, and require exact
fresh failure/repair evidence for each changed declaration. No such broader
permission is granted by this record.

**Not yet clear to merge — these provider proof proposals remain unapplied and uncompiled.**
''')
    sums(PROPOSALS)
    readme = UNIT / 'README.md'
    text = readme.read_text()
    text = text.replace('The immutable [issued brief]',
        'The [corrected received-source seal request plan](checkpoints/partial-r1/corrected-seal-plan-r1/README.md) is filed as unrun data for all123 required owners. [Three concrete provider proof proposals](checkpoints/partial-r1/provider-proposals-r1/README.md) remain unapplied.\nThe immutable [issued brief]')
    readme.write_text(text)
    handoff = MAIN / 'briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md'
    text = handoff.read_text()
    old = 'Corrected123-owner seal plans are in preparation;'
    new = ('Corrected received-source123-owner request plan is filed in `corrected-seal-plan-r1/`:102,875 pairs, '
           '154 helper requests restored and7,544 added for25 providers; DATA only, with inherited instance/reducible limits '
           'explicit and no runtime claims. Three standalone provider proof patches are directly reviewable in `provider-proposals-r1/`;')
    assert text.count(old) == 2
    handoff.write_text(text.replace(old, new))
    plan = MAIN / 'PassShelatChapter5-8Plan.md'
    plan.write_text(plan.read_text() + '| 2026-11-08 (PST) | **Corrected received-source seal request data and provider proposals filed.** '
        '`checkpoints/partial-r1/corrected-seal-plan-r1/`:123 owner plans/102,875 actual-component requests, '
        'existing98 restored to95,331 (+154 eval helpers),25 missing providers add7,544;4 empty lists explicit. '
        'All221 native TCS closure/name sets reconcile; inherited omissions retained, including5,129 semireducible instance pairs/118 identities '
        'and separate reducible/opaque limits. Optional108,004 instance-inclusive DATA has missing instance components explicitly null, '
        'no Name reconstruction/ruling/runtime pass. Source is received03ead, excludes local repairs. '
        'Three exact ClassNP provider proof proposals copied plainly under `provider-proposals-r1/`; all headers/data/costs/admissions unchanged, '
        'unapplied/uncompiled and no worker role expansion. Root124-module local check paused after cache+3 prerequisites when another host job '
        'appeared; same-phase source/object/log-verified resume waits for stable idle, preserving every attempt. | record |\n')
    git('diff', '--check')
    print(json.dumps({'plan_root': str(DEST), 'proposal_root': str(PROPOSALS),
                      'plan_archive_sha256': sha(archive.read_bytes()),
                      'status': 'WRITTEN_NOT_COMMITTED'}, indent=2))


if __name__ == '__main__':
    main()
