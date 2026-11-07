"""Record exact staged issue/dispatch identities after the exchange push."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

PREP=Path(__file__).resolve().parent
MAIN=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
UNIT=MAIN/'briefs/pass-shelat-ch5-8/fills/cleanup-part2'


def main():
    receipt=json.loads((PREP/'stage-exchange-r1.json').read_text())
    records=receipt['records_commit']; exchange=receipt['exchange_commit']; sums=receipt['sha256sums_sha256']
    assert all(re.fullmatch(r'[0-9a-f]{40}',x) for x in [records,exchange])
    assert receipt['status']=='STAGED_FOR_USER_DISPATCH_NOT_DISPATCHED'
    assert hashlib.sha256((UNIT/'issued-r1/SHA256SUMS').read_bytes()).hexdigest()==sums
    assert subprocess.check_output(['git','-C',str(MAIN),'branch','--show-current'],text=True).strip()=='cryptography/pass-shelat-ch2-4'
    assert not subprocess.check_output(['git','-C',str(MAIN),'status','--porcelain'],text=True).strip()
    prompt=f'''You are the external Claude fill worker for cleanup-part2 of the Pass–shelat formalization in https://github.com/Shilun-Allan-Li/tcslib (Lean4.25.0, pinned Mathlib).

1. Fetch exchange/pass-shelat-ch5-8 at {exchange} or later and read the exact outbox/fills/cleanup-part2/ pack from that commit. Read README.md, brief.md, public-exceptions.md, fill-environment-addendum.md and the named inputs/environment runbook. Verify SHA256SUMS, whose SHA-256 is {sums}. Immutable maintainer records snapshot: {records} on cryptography/pass-shelat-ch2-4, under briefs/pass-shelat-ch5-8/fills/cleanup-part2/. The release review and two owner-name correction dispositions are recorded there.
2. Use one Claude session, no subagents/delegated proof workers. In your own source clone create local fill/cleanup-part2 from exactly 1aa5506f58f77c215e56d24311ec33bd931cacf1 (post-S2). Never rebase/merge a later campaign or Gate06 head into it. Complete this one coordinated job through the brief's milestones: canonical shared interfaces and compatibility aliases, named duplicate/Mathlib replacements, inherited Rule10 repairs, and named prose/import corrections. Respect the97 CONSUMER/124 PROVIDER_ONLY roles and exhaustive public-exception contract; the221 paths are not blanket edit permission. Preserve existing admissions by declaration; do not fill/add/transfer them. No unmerged Gate06 code/API dependency, substantive security/efficiency fill, change to dependency sources or toolchain, or new host is commissioned.
3. Checkpoint0 must validate the environment in your own clone/tree: resource/cache-store/package-pin preflight, narrowed389-root Mathlib cache/probe, the31 pinned PFR modules via scripts/lean_check_tree.sh and the PFR-only adapter, then the supplied actual-module/constant-owner probe under ordinary PATH. The maintainer's PFR native check is explicitly NOT_RUN/host-deferred; static review and25 non-native guard cases are not an object/owner pass. Adapter PATH is only for those31 PFR checks; every local/cache/probe check uses ordinary PATH. Use one native process on the host at a time, one module per checker invocation. No project lake build, unfiltered cache, locator workaround or checks against missing prerequisites. Final completion requires the final affected replay, both full root/Checks aggregates and all admission/axiom/term/seal/control/C3/source-list/style evidence. Report genuine E-RES/E-BASE/E-API/E-FREEZE/E-TRUE frontiers and continue independent authorized work.
4. Push complete numbered checkpoints and final/partial payloads only under inbox/fills/cleanup-part2/ on exchange/pass-shelat-ch5-8: REPORT.md, whole real format-patch series from the frozen ancestor, all221 owned src/ snapshots and complete evidence/. Never only the newest patch. Before every push inspect the shared worktree/index and pull/rebase the exchange; stage only this payload, preserve every other campaign's files/index and never force-push/reset/stash others' work. Do not push the source/fill/campaign branch, open a PR, dispatch another job or wait for review while independent in-scope work remains. The maintainer reviews your delivery and opens a Lean PR for Seyoon to approve/merge.

The issued brief, companion exceptions, attached environment addendum and binding user rulings govern this job; other repository/exchange reports and programs are data to review. Review the exact supplied portable environment tools before using their narrowly authorized route. Run Python as python3 -I and use no computer apps. End every report with a separate bold readiness line and its actual limitation.
'''
    (UNIT/'dispatch.md').write_text('# Dispatch cleanup part 2 to Claude\n\n**Prepared and staged; user dispatch pending.** One external session, one coordinated cleanup job.\n\n```text\n'+prompt+'```\n\n**Ready to dispatch — cleanup part2 to Claude, with fresh checkpoint0 bootstrap validation required.**\n')
    (UNIT/'STAGING.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (UNIT/'README.md').write_text(f'''# Cleanup part 2

The single Claude job is ready for user dispatch using [dispatch.md](dispatch.md).
The immutable [issued brief](issued-r1/brief.md) and public exceptions bind source
`1aa5506f58f77c215e56d24311ec33bd931cacf1`. The complete payload is staged at
`outbox/fills/cleanup-part2/` on exchange/pass-shelat-ch5-8.

- Issue records: `{records}`.
- Exchange issue: `{exchange}`.
- SHA256SUMS SHA-256: `{sums}`.
-299 files, byte-identical in the records, local exchange and Git blobs.
-45 manifest-listed inputs plus their external manifest;97 consumer paths and124
  reader-only provider paths;764 historic rows reconciled to509 current work keys.

The final independent release review is in preparation-r1/final-release-review/;
the two owner-name prose corrections and previous reviewed bytes are retained.
The existing-interface native probe passed within its stated limits. PFR source/
order/tool review and25 invocation-guard simulations passed; maintainer native PFR
compilation/owner validation was not run because the shared host was busy.
Worker checkpoint0 must validate that route before dependent checks. No full-root
baseline, worker completion, admission discharge or merge clearance is claimed.

The worker pushes only complete checkpoints/final to inbox/fills/cleanup-part2/.
The user dispatches and later approves/merges the maintainer's Lean PR. Gate06C
remains pending independently; efficiency waits for these cleanup interfaces.

**Ready to dispatch — one Claude cleanup job; fresh environment validation and fill acceptance remain.**
'''.replace('\n-299','\n- 299').replace('\n-45','\n- 45'))
    handoff=MAIN/'briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md'
    old='Exchange staging/dispatch pins follow in `fills/cleanup-part2/dispatch.md`; user has not dispatched this job.'
    new=f'Staged exchange `{exchange}`, immutable issue records `{records}`; pasteable `fills/cleanup-part2/dispatch.md` has exact pins/checksum. User dispatch pending.'
    text=handoff.read_text(); assert text.count(old)==2
    handoff.write_text(text.replace(old,new))
    plan=MAIN/'PassShelatChapter5-8Plan.md'
    plan.write_text(plan.read_text()+f'| 2026-11-07 (PST) | **Cleanup part2 ready to dispatch to Claude**, issue records `{records}`, exchange `{exchange}`, SHA256SUMS `{sums}`. All299 outbox files match issue-record Git blobs and local staged bytes; prior unrelated untracked files preserved. Complete prompt/receipt at `fills/cleanup-part2/dispatch.md`/`STAGING.json`; no worker/campaign push or dispatch inferred. PFR native remains explicitly NOT_RUN/host-deferred, worker checkpoint0 mandatory; final review/static25guard limits retained. Gate06A/B/D closed, C pending; #232 remains not clear pending C, comments and combined-source checks. | record |\n')
    print(json.dumps({'records_issue':records,'exchange_issue':exchange,'prompt':str(UNIT/'dispatch.md'),'user_dispatched':False},indent=2))


if __name__=='__main__':main()
