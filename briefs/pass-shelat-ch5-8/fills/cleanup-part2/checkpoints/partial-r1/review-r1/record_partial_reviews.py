"""File immutable partial-delivery reviews and clearly separate local proposals."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

PREP = Path(__file__).resolve().parent
PART = PREP / 'partial-r1'
WORK = Path('/Users/seyoonr/.codex/worktrees/ps-gate08-repair/tcslib-pass-shelat-ch2-4')
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
UNIT = MAIN / 'briefs/pass-shelat-ch5-8/fills/cleanup-part2'
DEST = UNIT / 'checkpoints/partial-r1/review-r1'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


def archive(source, target):
    members = [(file.relative_to(source).as_posix(), file.read_bytes())
               for file in sorted(source.rglob('*'))
               if file.is_file() and '__pycache__' not in file.parts]
    with zipfile.ZipFile(target, 'x', zipfile.ZIP_DEFLATED, compresslevel=9) as zipped:
        for name, raw in members:
            info = zipfile.ZipInfo(name, date_time=(2026, 11, 8, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            zipped.writestr(info, raw)
    return {'archive': target.name, 'sha256': sha(target.read_bytes()),
            'files': [{'path': name, 'bytes': len(raw), 'sha256': sha(raw)} for name, raw in members]}


def main():
    assert git(MAIN, 'branch', '--show-current').decode().strip() == 'cryptography/pass-shelat-ch2-4'
    assert not git(MAIN, 'status', '--porcelain').strip()
    git(MAIN, 'pull', '--ff-only', 'origin', 'cryptography/pass-shelat-ch2-4')
    assert not git(MAIN, 'status', '--porcelain').strip() and not DEST.exists()
    DEST.mkdir()
    reviews = [
        ('review-source-scope', 'f15f33e8e264ad9eb3622df638ca9a411f816e08f6c26a767017ca17612f020b'),
        ('review-api-frontiers', 'dd7650240501aafc250e619c9c80b3d2fe85c515e5db0c0ff0611d5baa823f6c'),
        ('review-workflow', 'c1557d44149aa8ec24d9c5c1053515b523a87605fc8729e289b7ab0a8ff3411c'),
    ]
    manifests = []
    for name, expected in reviews:
        source = PART / name
        assert sha((source / 'report.md').read_bytes()) == expected, name
        manifests.append(archive(source, DEST / (name + '.zip')))
        for suffix in ['md', 'json']:
            (DEST / (name + '.' + suffix)).write_bytes((source / ('report.' + suffix)).read_bytes())
    manifests.append(archive(PART / 'provider-proof-proposals', DEST / 'provider-proof-proposals.zip'))
    manifests.append(archive(PART / 'gate06-merge-preview', DEST / 'gate06-merge-preview.zip'))
    # Preserve the concrete working proposals before another host frees Lean.
    assert git(WORK, 'branch', '--show-current').decode().strip() == 'cryptography/pass-shelat-cleanup-part2-final-review'
    assert git(WORK, 'rev-parse', 'HEAD').decode().strip() == 'bf2d8df1663f51c29a1d3c55ad8bf3fa56b74fe3'
    assert not git(WORK, 'diff', '--cached', '--name-only').strip()
    diff = git(WORK, 'diff', '--binary')
    assert sha(diff) == 'a082c09fba6118364014c2ac97a7b1a1d8b70a133fcd68e60d93f0d400306876'
    changed = git(WORK, 'diff', '--name-only').decode().splitlines()
    assert len(changed) == 8 and 'TCSlib/Complexity/ClassNP/PolyTime.lean' not in changed
    (DEST / 'local-eight-repairs-uncompiled.patch').write_bytes(diff)
    for name in ['local-review-branch.json', 'api01-local-repair.json']:
        (DEST / name).write_bytes((PART / name).read_bytes())
    native = PART / 'native-fixes-r1'
    assert not (native / 'RESULT.json').exists() and not (native / 'attempts.jsonl').exists()
    assert not Path(json.loads((native / 'config.json').read_text())['tree']).exists()
    manifests.append(archive(native, DEST / 'native-plan-host-deferred.zip'))
    for name in ['prepare_partial_native.py', 'run_partial_native.py', 'record_partial_reviews.py']:
        (DEST / name).write_bytes((PREP / name).read_bytes())
    (DEST / 'artifacts.json').write_text(json.dumps({
        'delivery': '0c4d4f60203021f3a3b93f88eaf7c9085c6ab885',
        'unique_received_review_findings': {'blockers': 0, 'majors': 5, 'minors': 3},
        'source_api_major_duplicate_counted_once': True, 'archives': manifests,
        'later_local_changes': {'files': changed, 'patch_sha256': sha(diff),
                                'native_status': 'NOT_RUN_SHARED_HOST_BUSY',
                                'source_pushed': False, 'PR_opened': False},
        'provider_proof_proposals_applied': False,
    }, indent=2) + '\n')
    (DEST / 'resolutions.md').write_text('''# Final-PARTIAL: maintainer resolutions r1

These dispositions concern received delivery0c4d4f60203021f3a3b93f88eaf7c9085c6ab885,
reported source03ead73ab38e74621800367c072f6fd3f0f70991. The delivery and three
bounded independent reports are preserved verbatim. Unique incoming findings:
**0 blockers,5 majors,3 minors**, counting the shared source/API major once.
No incoming program was executed and no received native claim is a maintainer run.

| Item | Disposition |
| --- | --- |
| Machine-body alias (source/API) | Open on received source. Its four-file operational-reader repair is applied to the isolated candidate, uncompiled on this new source. The earlier CP1 version passed101 native modules and six selected actual-axiom queries; that does not certify this later source. |
| P1 extra eval helpers | Open. Restore eval.match_1 and eval._sunfold, preserving the exact eval-only notation exception. Existing98-owner request count would be95,331, not95,177. Corrected plans are in preparation; no resulting failure count is inferred. |
| P2 omitted changed providers | Open. All97 consumers plus all26 changed providers require123 owner probes.25 changed providers were omitted. Provider failures remain observations, not permission to modify their proofs. |
| P3 incomplete source maps | Source pin is corrected in this delivery. The supplied map remains truncated. The source-review ZIP supplies full independent lexical base/head maps; complete actual-Name/dependency links and the eventual landing-source update remain required. |
| P4 overwritten attempt logs | Open within this payload:30 original failed development logs not located and four old seal logs replaced by later attempts. Originals may be supplied from elsewhere as a pinned supplement. Preserve metadata/summaries; never reconstruct later runs as the originals. Future attempts require exclusive paths and hashes. |
| P5 baseline source positions | Corrected by the independent recoverable line-map supplement, preserved in the workflow archive. All688 diagnostic positions are tied to exact raw probes. The correction does not change the strict canonical-block comparison. |
| P6 report qualifications | Recorded here: Checks axiom multisets equal; the all-stored census has the same29 admitted-dependent identities and five explained standard-axiom changes. The first N4 was invalid with No-goals errors, not a successful control pair.52 extra blocks means49 consumers plus3 providers. No blanket instance notation/eligibility ruling is inferred. |
| FRONTIER-01 unary escalation | Categorical impossibility not established. Four concrete existing BinArith/length-reader proposals are applied locally, uncompiled. Other inline-match sites remain unresolved; investigate named existing machine run/case contracts before requesting new general APIs. |

All13 patches independently reproduce all221 owned snapshots;122 changed paths
are96 consumers and26 providers. Existing provider declarations and all20 owned
admitted blocks remain byte-identical. The allowed body/header exceptions and
import graph pass the bounded lexical review. No mathematical/header/admission
defect beyond the known API shape was identified within that review; native,
instance, actual-Name and complete-source policy verification remain separate.

The received composite native evidence reconciles as581 affected modules plus
root/Checks at ea37eb57c28710271e41533d528309a6d7d00519, then51 delta modules plus
root/Checks at03ead73ab38e74621800367c072f6fd3f0f70991. This is not a single581
replay at the final source. Latest1,037 product/source/prerequisite records match.
Current controls/census/dispositions reconcile as data, not reproduced native work.
The strict501-to348 canonical-block comparison has zero new failing blocks; it
does not certify new reads inside already-failing blocks or unsealed providers.

The delivered measured-variant ledger now retains every509 key/764 original row:
333 measured repaired/verified keys,3 exact removals,173 open. Its225 failed blocks
partition into173 keyed declarations,49 additional consumers and3 providers.
The old CP1 denominator/count gap is resolved for that measured variant. Full
cleanup acceptance remains open, including the inherited instance-filter limit.
Pinned Lean reducibility-attribute source has no blanket semireducible-instance
rejection; no runtime eligibility/sensitivity pass is claimed here.

The candidate branch locally materializes the worker's13 commits with authorship,
at bf2d8df1663f51c29a1d3c55ad8bf3fa56b74fe3. Eight separate local edits remove the
new machine alias and repair four unary consumers through existing contracts.
Their full patch is preserved. The124-module cold check plan is complete; its
guard deferred before starting any Lean because other host work was active.
No candidate source was pushed, no PR was opened, and no new-source native
result is claimed. The old CP1 repair branch/objects remain preserved.

Three standalone ClassNP/PolyTime proof proposals are preserved separately.
They are **unapplied/uncompiled** and change only the id, output_length_le and
comp proofs through computesFunInTime_iff. Their statements, witnesses, costs,
imports and algorithms are unchanged. Original PROVIDER_ONLY worker permission
remains unchanged; any continuation scope exception is for the user to rule on.

A Git merge-tree preview of the received candidate and frozen Gate06 finds13
textual conflict paths. Temporary Git objects were written, but no ref/index/
working source changed. The preview excludes the later eight local edits and
does not replace semantic/API or native integration. Gate06C remains pending;
the audited head3f6db40e1688c4a0bb922c9575dd3bd2157a650b stays frozen.

The user has been asked which worker to use before preparing a new external
continuation. No continuation brief or dispatch is inferred from the recommended
answer, and no worker has been contacted. Independent authorized review/work
continues while that preference and the shared native host are pending.

**Not yet clear to merge — final-PARTIAL has outstanding repair/evidence work and the local follow-ups are not yet checked.**
''')
    (DEST / 'README.md').write_text('''# Final-PARTIAL independent review r1

Three verbatim bounded reports and their full own validation/source-map artifacts
are archived here. artifacts.json binds every ZIP/member. Unique findings are
0 blockers,5 majors,3 minors; source/API duplicate is counted once. See the
separate resolutions.md for corrected wording and exact open dispositions.

The local eight-repair patch and124-module check plan are preserved as uncompiled
work, separate from the received snapshot. Shared-host guards started no new
Lean process. Three provider-proof proposals remain unapplied. The merge preview
is informational only; no source branch was pushed or merged.

**Not yet clear to merge — received partial work and local verification remain open.**
''')
    sums = [f'{sha(file.read_bytes())}  {file.relative_to(DEST).as_posix()}'
            for file in sorted(DEST.rglob('*')) if file.is_file()]
    (DEST / 'SHA256SUMS').write_text('\n'.join(sums) + '\n')
    parent = UNIT / 'checkpoints/partial-r1/README.md'
    text = parent.read_text().replace('Independent source/freeze, workflow/evidence and API/frontier reviews are underway,',
        'Independent source/freeze, workflow/evidence and API/frontier reviews are archived in [review-r1](review-r1/README.md),')
    parent.write_text(text)
    readme = UNIT / 'README.md'
    text = readme.read_text().replace('independent review is underway.',
        '[independent review](checkpoints/partial-r1/review-r1/README.md) records five unique majors and three minors. Eight bounded local follow-ups await a shared native slot; provider proposals remain unapplied.')
    readme.write_text(text)
    handoff = MAIN / 'briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md'
    text = handoff.read_text()
    old = 'Independent source, evidence and frontier reviews are underway; no completion, source application or ruling is inferred.'
    new = ('Independent source/evidence/frontier reviews are filed in `checkpoints/partial-r1/review-r1/`: '
           'five unique majors/three minors, with raw maps/line corrections/log qualifications. '
           'All13 patches reproduce221 snapshots,122 authorized paths/26 providers; provider originals and20 admissions unchanged. '
           'Received native/census/control/disposition records reconcile as data;173 measured open keys remain. '
           'Local candidate `cryptography/pass-shelat-cleanup-part2-final-review` at '
           '`bf2d8df1663f51c29a1d3c55ad8bf3fa56b74fe3` preserves worker authorship; eight applied local repairs '
           'are uncommitted/uncompiled,124-module check deferred before any Lean due shared-host work. '
           'Three provider proof proposals are unapplied. Corrected123-owner seal plans are in preparation; '
           'Gate06 merge preview has13 textual conflicts, no source/ref/index changes. New continuation worker choice pending; '
           'no brief/dispatch/ruling/source push/PR/merge clearance inferred.')
    assert text.count(old) == 2
    handoff.write_text(text.replace(old, new))
    plan = MAIN / 'PassShelatChapter5-8Plan.md'
    plan.write_text(plan.read_text() + '| 2026-11-08 (PST) | **Final-PARTIAL independent review filed.** '
        'Three verbatim source/API/workflow reviews plus full own maps/validators at `checkpoints/partial-r1/review-r1/`: '
        '0 blockers/5 unique majors/3 minors. Source fidelity13 patches→221 snapshots,122 paths=96 consumers+26 providers, '
        'original provider declarations/20 admissions preserved. Open: machine-body API,2 extra eval-helper omissions,25 unsealed changed providers, '
        'truncated maps, overwritten attempt logs.509-key/764-row measured ledger/count gap resolved; recovered688 baseline source positions; '
        'N4/report/instance-filter qualifications retained. Recorded581+51 native composite/Checks/census/controls reconcile as data, '
        '173 measured keys remain open. Eight local consumer/API repairs and124-module fresh plan preserved uncompiled, '
        'guard started no Lean while shared host busy;3 exact provider proof proposals unapplied. '
        'Read-only-worktree Git merge preview has13 conflicts against frozen Gate06;C pending. '
        'Asked new continuation worker choice per standing rule before preparing a new fill; no dispatch/ruling/PR/source push/clearance. | record |\n')
    git(MAIN, 'diff', '--check')
    print(json.dumps({'record_root': str(DEST), 'archive_count': len(manifests),
                      'status': 'WRITTEN_NOT_COMMITTED', 'source_changes_in_records': False}, indent=2))


if __name__ == '__main__':
    main()
