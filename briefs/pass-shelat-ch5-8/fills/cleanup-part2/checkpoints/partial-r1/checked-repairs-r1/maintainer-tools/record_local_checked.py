"""Archive checked maintainer repairs, without treating partial work as accepted."""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import zipfile

PREP = Path(__file__).resolve().parent
PART = PREP / 'partial-r1'
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
WORK = Path('/Users/seyoonr/.codex/worktrees/ps-gate08-repair/tcslib-pass-shelat-ch2-4')
UNIT = MAIN / 'briefs/pass-shelat-ch5-8/fills/cleanup-part2'
DEST = UNIT / 'checkpoints/partial-r1/checked-repairs-r1'
HEAD = '32b827c017bc321ea40577bc8f27131df2c35e1a'
BASE = 'bf2d8df1663f51c29a1d3c55ad8bf3fa56b74fe3'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


def load(path):
    return json.loads(path.read_text())


def archive(source, target):
    members = []
    for file in sorted(source.rglob('*')):
        assert not file.is_symlink(), file
        if file.is_file() and '__pycache__' not in file.parts:
            members.append((file.relative_to(source).as_posix(), file.read_bytes()))
    with zipfile.ZipFile(target, 'x', zipfile.ZIP_DEFLATED, compresslevel=9) as zipped:
        for name, raw in members:
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 8, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            zipped.writestr(info, raw)
    return {'archive': target.name, 'sha256': sha(target.read_bytes()),
            'files': [{'path': name, 'bytes': len(raw), 'sha256': sha(raw)}
                      for name, raw in members]}


def main():
    assert git(MAIN, 'branch', '--show-current').decode().strip() == 'cryptography/pass-shelat-ch2-4'
    assert not git(MAIN, 'status', '--porcelain').strip()
    git(MAIN, 'pull', '--ff-only', 'origin', 'cryptography/pass-shelat-ch2-4')
    assert not git(MAIN, 'status', '--porcelain').strip() and not DEST.exists()
    assert git(WORK, 'rev-parse', 'HEAD').decode().strip() == HEAD
    assert git(WORK, 'branch', '--show-current').decode().strip() == 'cryptography/pass-shelat-cleanup-part2-final-review'
    assert not git(WORK, 'status', '--porcelain').strip()
    repairs = PART / 'local-repairs-final-r1'
    receipt = load(repairs / 'commit.json')
    assert receipt['head'] == HEAD and not receipt['full_cleanup_accepted']
    manifest = load(repairs / 'manifest.json')
    for item in manifest['files']:
        raw = (WORK / item['path']).read_bytes()
        assert sha(raw) == item['sha256']
        assert raw == (repairs / 'src' / item['path']).read_bytes()
    assert sha(git(WORK, 'diff', '--binary', BASE, HEAD)) == manifest['patch_sha256']
    native = PART / 'native-fixes-r1'
    result = load(native / 'RESULT.json')
    assert result['all_passed'] and result['source_revision'] == 3
    assert result['checked_local_modules'] == 124 and result['historical_failed_attempts'] == 2
    assert sha((native / 'attempts.jsonl').read_bytes()) == result['attempts_sha256']
    rows = [json.loads(line) for line in (native / 'attempts.jsonl').read_text().splitlines()]
    latest = {row['module']: row for row in rows}
    assert len(rows) == 127 and len(latest) == 125
    assert all(row['passed'] and row['rc'] == 0 for row in latest.values())
    assert sum(not row['passed'] for row in rows) == 2
    for row in rows:
        assert sha((native / row['log']).read_bytes()) == row['log_sha256']
    modules = load(native / 'modules-revision03.json')
    tree = Path(result['tree'])
    for module in modules:
        name = module['module']
        assert sha((WORK / (name + '.lean')).read_bytes()) == module['source_sha256']
        row = latest[name]
        assert row['source_sha256'] == module['source_sha256']
        assert sha((tree / (name + '.olean')).read_bytes()) == row['object_sha256']
        for prereq, digest in row['direct_prerequisites'].items():
            assert sha((tree / (prereq + '.olean')).read_bytes()) == digest
    axioms = load(native / 'SelectedAxioms-result.json')
    instance = load(native / 'InstanceEligibility-result.json')
    assert axioms['passed'] and axioms['standard_only'] and len(axioms['axioms']) == 10
    assert all(set(a) == {'propext', 'Classical.choice', 'Quot.sound'} for a in axioms['axioms'].values())
    assert instance['passed'] and instance['eligibility_verified']
    for probe in [axioms, instance]:
        assert sha((native / probe['log']).read_bytes()) == probe['log_sha256']
    review = PART / 'local-repairs-review-r1'
    assert sha((review / 'report.md').read_bytes()) == '1e4167a31d3ec3a41e8adcaab543e038e4826018edf23ca3d767d453c2e0cb77'
    assert load(review / 'report.json')['verdict'] == {'blockers': 0, 'majors': 0, 'minors': 0}
    assert load(PART / 'local-style-delta/result.json')['zero_new_normalized_findings']
    DEST.mkdir()
    archives = [archive(native, DEST / 'native-evidence.zip'),
                archive(repairs, DEST / 'checked-source.zip'),
                archive(review, DEST / 'independent-local-review.zip'),
                archive(PART / 'local-style-delta', DEST / 'local-style-delta.zip')]
    for name in ['report.md', 'report.json']:
        (DEST / ('independent-local-' + name)).write_bytes((review / name).read_bytes())
    for name in ['RESULT.json', 'SelectedAxioms-result.json', 'InstanceEligibility-result.json']:
        (DEST / name).write_bytes((native / name).read_bytes())
    for name in ['commit.json', 'checked-repair.patch', 'cumulative-source.patch', 'manifest.json']:
        (DEST / name).write_bytes((repairs / name).read_bytes())
    helpers = ['prepare_partial_native.py', 'run_partial_native.py',
               'prepare_native_resume.py', 'run_partial_native_resume.py',
               'check_oneway_attempt02.py', 'prepare_native_revision02.py',
               'run_partial_native_revision02.py', 'prepare_native_revision03.py',
               'run_partial_native_revision03.py', 'run_partial_probes.py',
               'check_local_style_delta.py', 'record_local_checked.py']
    tool_dir = DEST / 'maintainer-tools'
    tool_dir.mkdir()
    for name in helpers:
        (tool_dir / name).write_bytes((PREP / name).read_bytes())
    for name, probe in [('SelectedAxioms.lean.txt', axioms), ('InstanceEligibility.lean.txt', instance)]:
        (DEST / name).write_text(probe['source'])
    (DEST / 'artifacts.json').write_text(json.dumps({
        'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'worker_delivery': '0c4d4f60203021f3a3b93f88eaf7c9085c6ab885',
        'materialized_worker_head': BASE, 'checked_head': HEAD,
        'branch': receipt['branch'], 'archives': archives,
        'native_latest_module_results': 124, 'cache_probe': True,
        'historical_native_failures_retained': 2,
        'selected_actual_axiom_sets': 10, 'selected_standard_only': True,
        'local_static_review': {'blockers': 0, 'majors': 0, 'minors': 0},
        'local_style_new_findings': 0,
        'instance_example': 'Turing.instInhabitedCfg accepts local irreducibility',
        'provider_proof_proposals_applied': False,
        'corrected_seals_or_full_affected_root_checks_replayed': False,
        'source_pushed_at_this_record': False, 'PR_opened_at_this_record': False,
        'full_cleanup_accepted': False,
    }, indent=2) + '\n')
    (DEST / 'README.md').write_text('''# Checked local repairs to the partial delivery

The user-requested watch received Claude's final-PARTIAL delivery
`0c4d4f60203021f3a3b93f88eaf7c9085c6ab885`. Its thirteen attributed commits are
materialized at `bf2d8df1663f51c29a1d3c55ad8bf3fa56b74fe3`. Maintainer commit
`32b827c017bc321ea40577bc8f27131df2c35e1a` on
`cryptography/pass-shelat-cleanup-part2-final-review` adds eight checked repairs.
This record precedes pushing that source and opening a draft PR. The original
delivery and incoming reviews remain immutable, including their historical
uncompiled/deferred descriptions. A later PR receipt records publication.

The local delta removes a newly introduced whole-machine body equality, replaces
three uses with the existing operational output contract, and rewrites four
unary-multiplication efficiency proofs using existing BinArith polynomial-time
composition and length contracts. The latter checks refute the report's blanket
claim that these four sites need a new API. They preserve empty/malformed input
behavior and every retained public statement, algorithm, cost and admission.
No original provider proof is changed. All three provider proposals remain
unapplied; they are not part of this commit or a granted continuation exception.

Independent static review of the pinned eight-file delta found **0 blockers,
0 majors,0 minors**. It checks exact patch replay, frozen retained headers/data/
attributes, all20 owned admitted blocks, and the1,071-module import graph. It
does not certify the complete worker payload or adopt Root's native results.
The incoming source/API major is resolved in this overlay. The four workflow
majors and the broader inherited-read work remain open; the frozen incoming
five-major/three-minor finding count is not rewritten as a global clean bill.

## Native evidence and limits

Root checked the eight targets and their complete124-module local import
closure one module at a time using scripts/lean_check_tree.sh. The TCSlib tree
started empty; it was resumed after shared-host waits and two corrected failed
proof attempts. No TCSlib objects were copied from an older phase. It is a
single phase with verified resumes, not an uninterrupted run. All latest124
module results and the72-root Mathlib import probe pass. Every current local
source/object/direct-local-prerequisite hash was reconciled before archival.
Pinned external package identities and existing cache presence were checked;
the per-attempt dependency hashes cover local TCSlib objects, not every external
binary. No new Mathlib fetch or PFR bootstrap was necessary for these targets.

All127 native attempt rows and unique raw logs remain:125 latest distinct
modules including the cache probe, plus two earlier failures. The OneWay proof
first needed an explicit public congr transfer; the Encoding proof then needed
the Closure import owning that contract. Both failures, their corrected attempts,
the three source/config revisions and all resume reconciliations are archived.
STOP.json is a retained historical failure pointer; RESULT.json revision3 is the
completed current result. Own calls were serial and deferred for observed host
work; these records do not certify every other chat's unobserved activity.

Ten selected actual axiom sets are exactly propext, Classical.choice and
Quot.sound, with no sorryAx. They include all four repaired unary efficiency
lemmas and the operational reader endpoints. This is a selected check, not a
complete current-source axiom census. Local style comparison against received
bytes adds zero normalized findings; inherited file-size/API findings remain.

A separate native eligibility probe shows that the exact semireducible instance
Turing.instInhabitedCfg accepts a local irreducible attribute without unsafe
options. This contradicts a blanket marking-impossibility claim. It establishes
one instance's eligibility, not a complete instance sensitivity run, a notation
classification or a new scope ruling. The corrected123-owner request plan remains
unrun DATA; its inherited instance/reducible/opaque limits still require work.

## Remaining acceptance work

The received measured variant reports173 of509 keys still open. These local
repairs have not been used to claim a refreshed denominator or ledger closure.
Full current-source affected/root/Checks replay, complete seals including25
previously omitted changed providers and154 missing eval-helper requests,
complete actual-Name/source/dependency maps, controls/census/dispositions and
log-retention dispositions remain necessary. Missing old raw logs may still be
provided as a pinned supplement; later reruns cannot become those originals.

Gate06C remains pending at the frozen audited head. The13-conflict merge preview
is informational and excludes this later local delta; integration is separate.
The continuation worker choice and provider-proof scope ruling are pending with
the user. No continuation job is prepared/dispatched and no source is merged.

artifacts.json binds every archive member; SHA256SUMS binds this record. Probes
are recorded as text or inside ZIPs, with no Lean source added to the records
branch. Frozen incoming reports and the issued pack are unchanged.

**Not yet clear to merge — the local repairs are checked; full cleanup and seal acceptance remain incomplete.**
''')
    sums = [f'{sha(file.read_bytes())}  {file.relative_to(DEST).as_posix()}'
            for file in sorted(DEST.rglob('*')) if file.is_file()]
    (DEST / 'SHA256SUMS').write_text('\n'.join(sums) + '\n')

    readme = UNIT / 'README.md'
    text = readme.read_text()
    split = text.index('The immutable [issued brief]')
    text = '''# Cleanup part 2

Claude's [final-PARTIAL delivery](checkpoints/partial-r1/README.md) arrived during
the requested30-minute watch. The [incoming review](checkpoints/partial-r1/review-r1/README.md)
records five unique majors and three minors; it remains immutable history.
The [checked local follow-up](checkpoints/partial-r1/checked-repairs-r1/README.md)
at `32b827c017bc321ea40577bc8f27131df2c35e1a` removes the new raw-machine equality,
uses operational contracts and repairs four unary efficiency proofs through
existing APIs. Its124-module closure and ten selected actual axiom sets pass;
bounded independent static review is0B/0M/0m and local style adds no findings.
The broader partial cleanup and four workflow majors remain open. The earlier
[CP0](checkpoints/cp0/README.md), [CP1](checkpoints/cp1/README.md),
[CP1 review](checkpoints/cp1/review-r1/README.md),
[101-module CP1 repair](checkpoints/cp1/api01-native-r1/README.md) and
[509-key provisional index](checkpoints/cp1/dispositions-r1/README.md) are retained;
the final delivery resolves the old ledger denominator gap for its measured variant.

The [123-owner request plan](checkpoints/partial-r1/corrected-seal-plan-r1/README.md)
is unrun received-source DATA. [Three provider proof proposals](checkpoints/partial-r1/provider-proposals-r1/README.md)
remain unapplied. Continuation worker choice and provider scope ruling are pending;
no new job or worker permission is inferred. Publication of a draft source PR is
the next maintainer step; full cleanup acceptance is not granted by these checks.

''' + text[split:]
    text = text.replace('**Not yet clear to merge — the final-PARTIAL delivery is under review and inherited-read work remains.**',
        '**Not yet clear to merge — bounded repairs pass; full cleanup and corrected seal evidence remain incomplete.**')
    readme.write_text(text)
    parent = UNIT / 'checkpoints/partial-r1/README.md'
    text = parent.read_text()
    text = text.replace('**Not yet clear to merge — final-PARTIAL delivery received; independent review and incomplete work remain.**',
        'The later [checked maintainer repairs](checked-repairs-r1/README.md) are separate\nfrom this immutable intake. Their124-module closure and ten selected axiom checks\npass; full cleanup and seal acceptance remain open.\n\n'
        '**Not yet clear to merge — partial delivery reviewed and local repairs checked; full acceptance remains open.**')
    parent.write_text(text)
    dispatch = UNIT / 'dispatch.md'
    text = dispatch.read_text().replace('**Not yet clear to merge — the final-PARTIAL delivery is received and independent review is underway.**',
        '**Not yet clear to merge — delivery reviewed and bounded repairs checked; continuation choices and full cleanup evidence remain open.**')
    dispatch.write_text(text)
    handoff = MAIN / 'briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md'
    lines = handoff.read_text().splitlines(keepends=True)
    count = 0
    new = ('**Cleanup part2 final-PARTIAL received** during the requested30-minute watch: '
           'delivery `0c4d4f60203021f3a3b93f88eaf7c9085c6ab885`,13 attributed worker commits, '
           '221 snapshots/122 changed paths,26 providers with originals and20 admissions preserved. '
           'CP0/CP1/intake and three frozen bounded reports are under `fills/cleanup-part2/checkpoints/`; '
           'incoming verdict five unique majors/three minors. Worker measured ledger retains509 keys/764 rows,173 keys open; '
           'the old denominator gap is resolved for that variant. Checked maintainer head '
           '`32b827c017bc321ea40577bc8f27131df2c35e1a` on `cryptography/pass-shelat-cleanup-part2-final-review` '
           'preserves all13 worker commits and adds eight repairs: removes new raw-machine equality, '
           'uses operational readers and repairs four unary efficiency proofs with existing BinArith/length APIs. '
           '`checkpoints/partial-r1/checked-repairs-r1/` binds124 fresh local-module checks with verified same-phase resumes, '
           'two retained failed attempts, ten standard-only actual axiom sets, local0B/0M/0m review and zero new style findings. '
           'Native instance eligibility refutes blanket marking impossibility for one exact instance; not full sensitivity or a ruling. '
           'Four workflow majors/full current-source cleanup evidence remain:123-owner seals,154 restored eval helpers, '
           '25 omitted changed providers, instance coverage, full maps, raw-log dispositions, refreshed controls/census/ledger/root/Checks. '
           'Corrected request plans are unrun received-source DATA. Three exact provider proof proposals remain unapplied; '
           'continuation worker choice and provider scope ruling are pending. Draft source PR publication is next, '
           'no new external job/merge clearance. Gate06C and frozen3f6 head remain independent;13-conflict preview excludes local repairs. '
           'Issued pack/pins unchanged. Efficiency waits for cleanup interfaces. |\n')
    for i, line in enumerate(lines):
        marker = '**Cleanup part2 Claude final-PARTIAL delivered**'
        if marker in line:
            lines[i] = line[:line.index(marker)] + new
            count += 1
    assert count == 2
    handoff.write_text(''.join(lines))
    plan = MAIN / 'PassShelatChapter5-8Plan.md'
    plan.write_text(plan.read_text() + '| 2026-11-08 (PST) | **Partial cleanup: eight bounded maintainer repairs checked and committed.** '
        'Head32b827c017bc321ea40577bc8f27131df2c35e1a preserves13 worker commits; '
        'operational-reader API correction and four unary efficiency proofs use existing contracts, '
        'zero original provider proof/header/data/admission changes. `checkpoints/partial-r1/checked-repairs-r1/` '
        'archives124-module fresh local closure with source/object/prerequisite-verified resumes,72-root cache probe, '
        'all127 attempt rows including two corrected failures, ten selected standard-only actual axiom sets, '
        'independent local0B/0M/0m review and zero new normalized style findings. '
        'One exact definition-instance accepts local irreducibility; blanket ineligibility is false, no complete sensitivity/notation ruling. '
        'Incoming five-major/three-minor reports unchanged; API major resolved only in overlay, four workflow majors/full cleanup still open. '
        'No refreshed173-key denominator/complete census/root/Checks/seal pass inferred. '
        'Provider proposals unapplied; continuation worker/scope questions pending; no new external job or merge clearance. '
        'Source draft PR publication is next; Gate06 head frozen pendingC. | record |\n')
    assert not any(path.suffix == '.lean' for path in DEST.rglob('*'))
    git(MAIN, 'diff', '--check')
    print(json.dumps({'record_root': str(DEST), 'checked_head': HEAD,
                      'archives': [{'archive': a['archive'], 'sha256': a['sha256']} for a in archives],
                      'status': 'WRITTEN_NOT_COMMITTED'}, indent=2))


if __name__ == '__main__':
    main()
