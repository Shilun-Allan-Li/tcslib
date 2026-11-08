"""Preserve the complete provisional retained-key index as D-0 records."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

PREP = Path(__file__).resolve().parent
SOURCE = PREP / 'cp1/review-dispositions'
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
UNIT = MAIN / 'briefs/pass-shelat-ch5-8/fills/cleanup-part2'
DEST = UNIT / 'checkpoints/cp1/dispositions-r1'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*args):
    return subprocess.check_output(['git', '-C', str(MAIN), *args], text=True).strip()


def main():
    assert git('branch', '--show-current') == 'cryptography/pass-shelat-ch2-4'
    assert not git('status', '--porcelain')
    git('pull', '--ff-only', 'origin', 'cryptography/pass-shelat-ch2-4')
    assert not git('status', '--porcelain') and not DEST.exists()
    assert sha((SOURCE / 'manifest.json').read_bytes()) == '9a0b6c849dce75261dac4d2eede4f20070b99dc5b5e9d07e2b8a776d8f9a4e63'
    assert sha((SOURCE / 'report.md').read_bytes()) == '600b1d29fbbab734e729d04a274e1bf85067b0a217dd6b42120c902a725b1845'
    manifest = json.loads((SOURCE / 'manifest.json').read_text())
    assert len(manifest['outputs']) == 17
    expected = {'manifest.json'}
    for row in manifest['outputs']:
        file = Path(row['path'])
        rel = file.relative_to(SOURCE).as_posix()
        raw = file.read_bytes()
        assert len(raw) == row['bytes'] and sha(raw) == row['sha256'], rel
        expected.add(rel)
    members = [(file.relative_to(SOURCE).as_posix(), file.read_bytes())
               for file in sorted(SOURCE.rglob('*'))
               if file.is_file() and '__pycache__' not in file.parts]
    assert {name for name, raw in members} == expected and len(members) == 18
    DEST.mkdir()
    archive = DEST / 'retained-key-index.zip'
    with zipfile.ZipFile(archive, 'x', zipfile.ZIP_DEFLATED, compresslevel=9) as zipped:
        for name, raw in members:
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 8, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            zipped.writestr(info, raw)
    for name in ['report.md', 'report.json', 'manifest.json']:
        (DEST / name).write_bytes((SOURCE / name).read_bytes())
    (DEST / 'archive-manifest.json').write_text(json.dumps({
        'archive_sha256': sha(archive.read_bytes()),
        'files': [{'path': name, 'bytes': len(raw), 'sha256': sha(raw)} for name, raw in members],
    }, indent=2) + '\n')
    (DEST / 'record_cp1_ledger.py').write_bytes(Path(__file__).read_bytes())
    (DEST / 'README.md').write_text('''# CP1 complete retained-key index

The own bounded data review retains all509 issued keys and all764 original row
objects/links exactly once. Every key remains OPEN_PROVISIONAL and every native
acceptance field UNKNOWN. This provides an index for later review, not proof or
worker completion credit, and does not resolve W4's acceptance/disposition work.

Source relations are206 unchanged,296 changed,4 moved and3 explicit replacement
links. No key has a missing current source target.17 raw diagnostics,48 source
scan items and12 lexical route candidates stay explicitly unresolved; no nearby
declaration or suffix is guessed. All received diagnostics and variant identities
remain visible. Counts from unmatched seal variants are not repair deltas.

The ZIP contains all17 original own review outputs and their external manifest,
including the complete matrix,
historical-row objects, source/move/alias links, ambiguities and Python validators.
The report and manifests are also copied verbatim. The immutable CP1 is the sole
head analyzed; the later checked local API-01 commit is excluded. No native test
or incoming code execution occurred in this review.

**Not yet clear to merge — all issued keys are retained, and their acceptance remains open.**
''')
    sums = [f'{sha(file.read_bytes())}  {file.relative_to(DEST).as_posix()}'
            for file in sorted(DEST.rglob('*')) if file.is_file()]
    (DEST / 'SHA256SUMS').write_text('\n'.join(sums) + '\n')
    readme = UNIT / 'README.md'
    text = readme.read_text()
    text = text.replace('The user requested30-minute checks for the next partial delivery.',
        'The [complete provisional index](checkpoints/cp1/dispositions-r1/README.md) retains all509 keys/764 rows without closing any. The user requested30-minute checks for the next partial delivery.')
    readme.write_text(text)
    plan = MAIN / 'PassShelatChapter5-8Plan.md'
    plan.write_text(plan.read_text() + '| 2026-11-08 (PST) | **CP1 retained-key index complete, acceptance still open.** '
        'Independent immutable-CP1 matrix preserves all509 issued key objects and764 original row objects/links exactly once; '
        '206 unchanged/296 changed/4 moved/3 explicit replacements, zero missing current source targets. '
        'All statuses OPEN_PROVISIONAL/native UNKNOWN, zero closures.17 raw diagnostic mappings,48 scan items and12 lexical route candidates '
        'remain explicit unresolved; raw variant observations/754 source deltas/9 moves/8 exact X1 alias links retained. '
        'Artifacts/own validators archived in `checkpoints/cp1/dispositions-r1/`; no received program/native/source mutation. '
        'Later local API-01 repair excluded. Index supports the upcoming partial comparison and does not discharge W4 or the final ledger. | record |\n')
    git('diff', '--check')
    print(json.dumps({'record_root': str(DEST), 'archive_bytes': archive.stat().st_size,
                      'archive_sha256': sha(archive.read_bytes()), 'status': 'WRITTEN_NOT_COMMITTED'}, indent=2))


if __name__ == '__main__':
    main()
