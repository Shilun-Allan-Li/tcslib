"""Record draft publication after live verification; never grant merge clearance."""
from pathlib import Path
import hashlib
import json
import subprocess

PREP = Path(__file__).resolve().parent
PART = PREP / 'partial-r1'
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
UNIT = MAIN / 'briefs/pass-shelat-ch5-8/fills/cleanup-part2'
DEST = UNIT / 'checkpoints/partial-r1/draft-pr-r1'


def git(*args):
    return subprocess.check_output(['git', '-C', str(MAIN), *args], text=True).strip()


def main():
    assert git('branch', '--show-current') == 'cryptography/pass-shelat-ch2-4'
    assert not git('status', '--porcelain')
    git('pull', '--ff-only', 'origin', 'cryptography/pass-shelat-ch2-4')
    assert not git('status', '--porcelain') and not DEST.exists()
    receipt = json.loads((PART / 'source-publication.json').read_text())
    live = json.loads((PART / 'draft-pr-live.json').read_text())
    assert receipt['PR_number'] == live['number'] == 248
    assert live['isDraft'] and live['state'] == 'OPEN' and live['mergedAt'] is None
    assert live['headRefOid'] == '32b827c017bc321ea40577bc8f27131df2c35e1a'
    assert live['baseRefName'] == 'cryptography/pass-shelat-ch2-4'
    DEST.mkdir()
    for name in ['source-publication.json', 'draft-pr-live.json', 'draft-pr-body.md']:
        (DEST / name).write_bytes((PART / name).read_bytes())
    (DEST / 'record_draft_pr.py').write_bytes(Path(__file__).read_bytes())
    (DEST / 'README.md').write_text('''# Partial cleanup draft PR publication

[PR #248](https://github.com/Shilun-Allan-Li/tcslib/pull/248) is open and **draft**,
targeting cryptography/pass-shelat-ch2-4 from
cryptography/pass-shelat-cleanup-part2-final-review at
`32b827c017bc321ea40577bc8f27131df2c35e1a`. Its13 worker commits preserve attribution;
one maintainer commit adds the eight checked repairs. The PR contains122 changed
Lean paths and no new records files relative to its campaign merge base.
The13 worker source commits were materialized atop an existing records commit;
there are14 new code commits relative to the current campaign base, not a claim
that no earlier records commits exist since the issued source ancestor.

The GitHub connector's create operation returned403 Resource not accessible by
integration. Authenticated GitHub CLI creation succeeded. The exact description,
live CLI response and publication receipt are retained here; no computer app was
used, no worker was contacted, and no merge or auto-merge was requested.
GitHub's textual MERGEABLE/CLEAN result is not campaign merge clearance.

[The checked repairs record](../checked-repairs-r1/README.md), pinned at records
commit302d9ed57828cf901d9be3dc26c8f0ec8f8a74ab, binds the124-module closure,
ten selected standard-only actual axiom sets, static local0B/0M/0m review,
zero new normalized local style findings and both retained corrected failures.
These bounded checks leave full cleanup acceptance open. Original incoming
reviews remain unchanged; their API major is resolved in this overlay while
four workflow majors and further inherited-read work remain.

The expected partial delivery arrived and the requested watch has served its
purpose. No periodic automation or future background watch is claimed. The
maintainer has asked the user for the continuation worker choice and whether
proof-only repairs of freshly witnessed original-provider Rule10 reads may be
allowed. Both choices remain pending; three exact provider proposals are
unapplied, no new fill brief is issued, and no recommended answer is inferred.
Gate06C remains pending at its separate frozen audited head. Efficiency waits
for the cleanup interfaces; downstream integration/merge decisions stay separate.

**Not yet clear to merge — PR #248 preserves checked partial work; full cleanup, seal evidence and continuation choices remain open.**
''')
    rows = [f'{hashlib.sha256(file.read_bytes()).hexdigest()}  {file.relative_to(DEST).as_posix()}'
            for file in sorted(DEST.rglob('*')) if file.is_file()]
    (DEST / 'SHA256SUMS').write_text('\n'.join(rows) + '\n')
    readme = UNIT / 'README.md'
    text = readme.read_text()
    old = ('no new job or worker permission is inferred. Publication of a draft source PR is\n'
           'the next maintainer step; full cleanup acceptance is not granted by these checks.')
    new = ('no new job or worker permission is inferred. [Draft PR #248](https://github.com/Shilun-Allan-Li/tcslib/pull/248)\n'
           'is published at the checked head; its [publication receipt](checkpoints/partial-r1/draft-pr-r1/README.md)\n'
           'binds the exact description and live draft/head/base verification. Full cleanup\n'
           'acceptance is not granted by these checks. The expected partial delivery has\n'
           'arrived; no future background watch is claimed.')
    assert old in text
    readme.write_text(text.replace(old, new))
    parent = UNIT / 'checkpoints/partial-r1/README.md'
    text = parent.read_text().replace('pass; full cleanup and seal acceptance remain open.',
        'pass; [draft PR #248](draft-pr-r1/README.md) is published for review. Full\ncleanup and seal acceptance remain open.')
    parent.write_text(text)
    dispatch = UNIT / 'dispatch.md'
    text = dispatch.read_text()
    first = '**Claude final-PARTIAL delivery received.**'
    assert first in text
    text = text.replace(first, first + ' The reviewed candidate and checked bounded repairs are published as [draft PR #248](https://github.com/Shilun-Allan-Li/tcslib/pull/248); full acceptance remains open.', 1)
    dispatch.write_text(text)
    handoff = MAIN / 'briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md'
    text = handoff.read_text()
    old = 'Draft source PR publication is next, no new external job/merge clearance.'
    assert text.count(old) == 2
    text = text.replace(old, 'Draft [PR #248](https://github.com/Shilun-Allan-Li/tcslib/pull/248) is published at the checked head; `draft-pr-r1/` binds live draft/head/base verification. Expected delivery/watch fulfilled; no future background monitor, new external job or merge clearance.')
    handoff.write_text(text)
    plan = MAIN / 'PassShelatChapter5-8Plan.md'
    plan.write_text(plan.read_text() + '| 2026-11-08 (PST) | **Partial cleanup preserved in draft PR #248.** '
        'Live CLI verification:OPEN/draft,base cryptography/pass-shelat-ch2-4,head32b827c017bc321ea40577bc8f27131df2c35e1a; '
        '14 new code commits (13 attributed worker plus bounded maintainer repairs),122 Lean paths/no new records in PR diff. '
        'GitHub connector create403 fell back to authenticated CLI; exact body/live receipt filed in `checkpoints/partial-r1/draft-pr-r1/`. '
        'Evidence record302d9ed57828cf901d9be3dc26c8f0ec8f8a74ab binds124-module/ten-selected-axiom passes and two retained failures. '
        'Partial arrival and requested watch fulfilled, no future background monitoring claimed. '
        'Continuation worker choice/provider-proof scope ruling pending; no new brief/dispatch/provider repair/full seal pass or merge clearance. '
        'Gate06C/head remain separate and frozen. | record |\n')
    git('diff', '--check')
    print(json.dumps({'record_root': str(DEST), 'PR': 248,
                      'status': 'WRITTEN_NOT_COMMITTED', 'merge_clearance': False}, indent=2))


if __name__ == '__main__':
    main()
