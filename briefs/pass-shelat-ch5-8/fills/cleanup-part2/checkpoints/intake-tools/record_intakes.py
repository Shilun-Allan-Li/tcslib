"""File exact CP0/CP1 delivery archives as D-0 records, without source changes."""
from pathlib import Path
import hashlib
import json
import subprocess

PREP=Path(__file__).resolve().parent
MAIN=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
UNIT=MAIN/'briefs/pass-shelat-ch5-8/fills/cleanup-part2'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(MAIN),*args],text=True).strip()


def main():
    assert git('branch','--show-current')=='cryptography/pass-shelat-ch2-4'
    assert not git('status','--porcelain') and not git('diff','--cached','--name-only')
    for label in ['cp0','cp1']:
        src=PREP/label; target=UNIT/'checkpoints'/label
        meta=json.loads((src/'intake.json').read_text())
        assert not target.exists() and not meta['payload_checksum_issues']
        assert not meta['source_missing_owned'] and not meta['source_outside_owned']
        assert sha(src/'received.zip')==meta['archive_sha256']
        target.mkdir(parents=True)
        for name in ['received.zip','REPORT.md','PAYLOAD-SHA256SUMS','files.json','intake.json']:
            (target/name).write_bytes((src/name).read_bytes())
        (target/'README.md').write_text(f'''# Cleanup {label}: immutable intake

Claude delivery: `{meta['delivery_commit']}` on exchange/pass-shelat-ch5-8,
assigned subtree inbox/fills/cleanup-part2/. The received REPORT and supplied checksum
file are verbatim. received.zip is the maintainer's Git archive of that exact subtree,
not a worker-uploaded archive. files.json binds every raw Git blob, mode, size and SHA.

- Files: {meta['files']}; raw bytes: {meta['bytes']}.
- Archive SHA-256: `{meta['archive_sha256']}`.
- REPORT SHA-256: `{meta['report_sha256']}`.
- All supplied checksum entries verify after ordinary ./ path normalization.
- All221 owned source snapshots are present; no outside-owned source snapshot.

Intake does not execute received programs, apply source, reproduce native work or
accept worker verification claims. Reviews follow separately. CP0's whole-file seal
is now disclosed by CP1 as a strict variant including PolyExpr.eval; it is not the
approved-standard comparator. CP1 remains an intermediate delivery with unresolved
inherited reads and incomplete final evidence. No merge clearance.

**Not yet clear to merge — immutable delivery intake only; independent reviews remain.**
''')
    record_tools=UNIT/'checkpoints/intake-tools'
    record_tools.mkdir()
    for name in ['intake_delivery.py','record_intakes.py']:
        (record_tools/name).write_bytes((PREP/name).read_bytes())
    # Replace only stale current-status text; original issued packet stays immutable.
    handoff=MAIN/'briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md'
    text=handoff.read_text()
    start='**Cleanup part 2: one Claude job prepared/issued r1**'
    ending='User dispatch pending.'
    new='**Cleanup part2 Claude fill active**, frozen source `1aa5506f58f77c215e56d24311ec33bd931cacf1`. CP0 `c2bb964b35668455e1ea7748b3ef9e312d70240c` and CP1 `8b133945c3ba4aa7abb3b896bec38441535959b2` are archived verbatim under `fills/cleanup-part2/checkpoints/`. Raw manifests/Git/ZIP integrity and221-source path sets verify. CP1 has seven patches and reports completed interface/dedup work, resumed development replay/root/Checks, and open inherited definition reads; independent source/API/workflow reviews are underway. CP0 worker PFR31 and full baseline1037 PASS receipts were inspected, without a maintainer cold replay. CP0 strict seal is not a standard-variant comparator; further CP1 methodology findings remain for separate review records. User requested30-minute checks for an upcoming partial delivery (2026-11-08 PST), followed by fruitful authorized work. Original issued pack/pins remain unchanged. No source applied/PR/merge clearance at intake.'
    assert text.count(start)==2
    for _ in range(2):
        a=text.index(start); b=text.index(ending,a)+len(ending)
        text=text[:a]+new+text[b:]
    handoff.write_text(text)
    dispatch=UNIT/'dispatch.md'; text=dispatch.read_text()
    text=text.replace('**Prepared and staged; user dispatch pending.** One external session, one coordinated cleanup job.',
        '**Active Claude fill.** Checkpoints0and1 received; the issued prompt below is retained for provenance. User requested30-minute monitoring for the upcoming partial delivery on2026-11-08 PST.')
    text=text.replace('**Ready to dispatch — cleanup part2 to Claude, with fresh checkpoint0 bootstrap validation required.**',
        '**Not yet clear to merge — Claude fill active; delivery review and inherited-read repairs remain.**')
    dispatch.write_text(text)
    readme=UNIT/'README.md'; text=readme.read_text()
    text=text.replace('The single Claude job is ready for user dispatch using [dispatch.md](dispatch.md).',
        'The single Claude job is active. The issued [prompt](dispatch.md) is retained for provenance; [CP0](checkpoints/cp0/README.md) and [CP1](checkpoints/cp1/README.md) are received, with independent CP1 reviews underway. The user requested30-minute checks for the next partial delivery.')
    text=text.replace('**Ready to dispatch — one Claude cleanup job; fresh environment validation and fill acceptance remain.**',
        '**Not yet clear to merge — CP1 is intermediate; review, inherited-read repair and final evidence remain.**')
    readme.write_text(text)
    plan=MAIN/'PassShelatChapter5-8Plan.md'
    plan.write_text(plan.read_text()+'| 2026-11-08 (PST) | **Cleanup Claude job active;30-minute partial-delivery watch requested by user.** CP0 `c2bb964b35668455e1ea7748b3ef9e312d70240c` (1542files, archiveSHA `488276e9d822789f690d8536f627a3212652f7cb54c5d778b00893d566bb9772`) and CP1 `8b133945c3ba4aa7abb3b896bec38441535959b2` (2914files, archiveSHA `b8686342674cb6b5258c39d064da43f5f6245d1e2e9f3e52adfe3af441f2af3e`) filed verbatim before resolutions. All manifest/Git/ZIP bytes match;221src paths each, no received program executed. CP0 baseline/PFR evidence was inspected without local cold replay; strict-seal comparator qualification retained. CP1 seven-patch source/API/workflow reviews started; reported interface/dedup completion and resumed dev/root/Checks passes remain worker claims pending review. Inherited reads/final controls/lints/ledger remain open. No Lean branch advance, new external dispatch, PR or merge clearance. | record |\n')
    print(json.dumps({'archived':['cp0','cp1'],'records_root':str(UNIT/'checkpoints'),'source_changes':False},indent=2))


if __name__=='__main__':main()
