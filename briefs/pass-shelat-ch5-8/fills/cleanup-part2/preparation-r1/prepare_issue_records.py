"""Copy reviewed issue bytes into D-0 records; does not stage/commit/push."""
from pathlib import Path
import hashlib
import json
import subprocess

PREP=Path(__file__).resolve().parent
MAIN=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
UNIT=MAIN/'briefs/pass-shelat-ch5-8/fills/cleanup-part2'
PACK=PREP/'issue-pack-r2'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args): return subprocess.check_output(['git','-C',str(MAIN),*args],text=True).strip()


def copy_tree(src,dst):
    assert not dst.exists()
    for path in sorted(src.rglob('*')):
        if path.is_file():
            assert not path.is_symlink()
            target=dst/path.relative_to(src)
            target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(path.read_bytes())
            assert sha(path)==sha(target)


def main():
    assert git('branch','--show-current')=='cryptography/pass-shelat-ch2-4'
    assert not git('status','--porcelain') and not git('diff','--cached','--name-only')
    release=PREP/'issue-release-review-r1'
    assert (release/'review.md').is_file() and (release/'review.json').is_file()
    final=json.loads((release/'finalrelease.json').read_text())
    assert final['severity_counts']=={'blockers':0,'majors':0,'minors':0}
    assert final['pack']['sha256sums_sha256']==sha(PACK/'SHA256SUMS')
    # Validate every externally listed pack byte before copying it.
    rows=(PACK/'SHA256SUMS').read_text().splitlines()
    expected={}
    for row in rows:
        digest,path=row.split('  ',1)
        assert (PACK/path).resolve().is_relative_to(PACK.resolve())
        assert sha(PACK/path)==digest
        expected[path]=digest
    assert set(expected)=={str(p.relative_to(PACK)) for p in PACK.rglob('*') if p.is_file()}-{'SHA256SUMS'}
    assert not any(p.endswith('.lean') for p in expected)
    copy_tree(PACK,UNIT/'issued-r1')
    copy_tree(release,UNIT/'preparation-r1/final-release-review')
    copy_tree(PREP/'issue-revision-r2',UNIT/'preparation-r1/issue-revision-r2')
    for name in ['issue-draft-r1','issue-draft-r2']:
        copy_tree(PREP/name,UNIT/'preparation-r1'/name)
    for name in ['assemble_issue.py','archive_interface.py','prepare_issue_records.py','finalize_issue_revision.py','stage_issue_exchange.py','finish_issue_records.py']:
        p=UNIT/'preparation-r1'/name
        p.write_bytes((PREP/name).read_bytes())
    draft=UNIT/'brief-draft.md'
    original=draft.read_bytes()
    (UNIT/'preparation-r1/legacy-brief-draft.md').write_bytes(original)
    draft.write_text('**Historical design draft — superseded by [issued r1](issued-r1/brief.md), prepared for one Claude session.**\n\n'+original.decode())
    handoff=MAIN/'briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md'
    old='**Cleanup part 2 worker: Claude**, selected by the user; preparation/reconciliation underway, not issued.'
    new='**Cleanup part 2: one Claude job prepared/issued r1**, source `1aa5506f58f77c215e56d24311ec33bd931cacf1`; `fills/cleanup-part2/issued-r1/brief.md` and final release review bind the exact scope. Source/ownership/tool reviews and selected existing native interface probe passed; PFR native bootstrap is explicitly host-deferred/NOT_RUN and required at worker checkpoint0. No full-root baseline, worker delivery or merge clearance claimed. Exchange staging/dispatch pins follow in `fills/cleanup-part2/dispatch.md`; user has not dispatched this job.'
    text=handoff.read_text()
    assert text.count(old)==2
    handoff.write_text(text.replace(old,new))
    plan=MAIN/'PassShelatChapter5-8Plan.md'
    row='| 2026-11-07 (PST) | **Cleanup part2 issued r1 for one Claude session**, source `1aa5506f58f77c215e56d24311ec33bd931cacf1`, under existing user worker choice/Q2(A). Complete764-row reconciliation gives509 current scheduling keys,97 consumer/124 reader-only provider paths;45 manifest-listed frozen inputs plus their DELIVERY manifest are exact. Exhaustive helper/three-definition exceptions, same-header/algorithm/admission freeze, complete checkpoints and final root/Checks/axiom/Rule10 requirements are explicit. New canonical APIs remain work targets; Gate06 overlap creates no unmerged dependency. Selected existing native interface probe passed; concrete31PFR/389Mathlib-root route passed static/invocation-guard review, but maintainer native launch was host-deferred75 before any PFR/cache run. Worker checkpoint0 must freshly validate bootstrap/ordinary-PATH owner probe before dependent checks. Pack SHA256SUMS `'+sha(PACK/'SHA256SUMS')+'`; final release review and all failed/probe limits preserved. Ready for staging/user dispatch, not dispatched or clear to merge; efficiency waits. | record |\n'
    plan.write_text(plan.read_text()+row)
    print(json.dumps({'pack_sha256sums':sha(PACK/'SHA256SUMS'),'pack_files':len(rows)+1,
                      'destination':str(UNIT/'issued-r1'),'git_head_before_commit':git('rev-parse','HEAD')},indent=2))


if __name__=='__main__': main()
