"""Assemble the reviewed issue pack, without native/Git/network execution."""
from pathlib import Path
import datetime
import hashlib
import json
import re

PREP = Path(__file__).resolve().parent
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
DEST = PREP/'issue-pack-r1'
BASE = '1aa5506f58f77c215e56d24311ec33bd931cacf1'


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def dump(path, value): path.write_text(json.dumps(value, indent=2)+'\n')
def copy(source, relative):
    out = DEST/relative
    assert out.resolve().is_relative_to(DEST.resolve()) and not out.exists(), relative
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_bytes(source.read_bytes())
    assert sha(out) == sha(source)
    return out


def declared(source, manifest_name, prefix):
    manifest = json.loads((source/manifest_name).read_text())
    paths = [manifest_name]+[r['path'] for r in manifest['files']]
    assert len(set(paths)) == len(paths)
    for row in manifest['files']:
        path = source/row['path']
        assert path.resolve().is_relative_to(source.resolve())
        assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256']
    for path in paths: copy(source/path, prefix+'/'+path)
    return paths


def main():
    DEST.mkdir(exist_ok=False)
    inputs = PREP/'issue-inputs-r1'
    assert sha(inputs/'DELIVERY-MANIFEST.json') == '994c8dc040cee2d4af24f20bcbe92b371e8a716ae041ccefe0f225980f51e168'
    assert sha(inputs/'INPUTS-MANIFEST.json') == '31252c0581393430bac7114751383e22ddab0cc63cbdba1af3da09b648218fb5'
    assert len(declared(inputs, 'DELIVERY-MANIFEST.json', 'inputs')) == 46  # 45 leaves plus their external manifest
    external = PREP/'external-bootstrap-r1'
    assert sha(external/'DELIVERY-MANIFEST.json') == '70dd1a408a2c0c46af7ab2da50ff50520b26b2983e298492935008debb1a2cbd'
    declared(external, 'DELIVERY-MANIFEST.json', 'external-bootstrap-r1')
    tools = PREP/'external-tools-r1'
    portable = ['prepare_pfr.py','pfr_lean.py','RUNBOOK.md','PFRIdentityProbe.source.txt']
    tool_rows = []
    for name in portable:
        out = copy(tools/name, 'environment-tools/'+name)
        tool_rows.append({'path': name, 'bytes': out.stat().st_size, 'sha256': sha(out)})
    tool_manifest = DEST/'environment-tools/MANIFEST.json'
    dump(tool_manifest, {'status': 'REVIEWED_PORTABLE_ENVIRONMENT_ROUTE_NOT_NATIVE_PASS',
         'ancestor': BASE, 'files': tool_rows,
         'executable_scope': ['prepare_pfr.py', 'pfr_lean.py'],
         'probe_scope': 'Scratch normal-PATH checker harness only; no public library module',
         'native_status': 'MAINTAINER_DEFERRED_HOST_BUSY; worker checkpoint0 required'})
    copy(MAIN/'briefs/pass-shelat-ch5-8/fills/fill-environment-addendum.md', 'fill-environment-addendum.md')
    for source, target in [
        ('policy.md','methodology/policy.md'),
        ('AGENTS.md','methodology/source-AGENTS.md'),
        ('briefs/pass-shelat-ch5-8/AGENTS.md','methodology/campaign-AGENTS.md'),
        ('briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md','methodology/MAINTAINER-HANDOFF.md'),
        ('briefs/pass-shelat-ch5-8/EXCHANGE.md','methodology/EXCHANGE.md'),
        ('briefs/pass-shelat-ch5-8/maintainer/tooling-followups.md','methodology/tooling-followups.md')]:
        copy(MAIN/source, target)
    # Exact closed same-chat probe artifacts, including the failed first attempt.
    interface = PREP/'preship-r1/interface'
    declared(interface, 'MANIFEST.json', 'preship/interface')
    copy(tools/'native_validation.py', 'preship/pfr/maintainer-native-validation.source.txt')
    pfr_status = DEST/'preship/pfr/STATUS.json'
    dump(pfr_status, {'status': 'DEFERRED_HOST_BUSY_NO_NATIVE_PFR_OR_CACHE_RUN',
        'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'ancestor': BASE, 'cache_get_started': False, 'pfr_native_checks_started': 0,
        'import_owner_probe_started': False, 'native_success_claimed': False,
        'attempts': [
            {'phase':'cache','attempt':'r1','return_code':75,'defer_native_host_busy_lean_pids':[78121]},
            {'phase':'cache','attempt':'r2','return_code':75,'defer_native_host_busy_lean_pids':[78121]},
            {'phase':'cache','attempt':'r3','return_code':75,'defer_native_host_busy_lean_pids':[78121,85556]}],
        'attempt_provenance':'Captured maintainer tool stdout; each gate stopped before configure/cache/native work. PIDs are observations, not jobs owned or interrupted by the maintainer.',
        'required_worker_validation':'Checkpoint0: own-clone narrowed cache/probe, all31PFR checks then ordinary-PATH module/constant owner probe before dependent checks.',
        'limit':'Static/guard review cannot establish successful module compilation, imported owner identity, full-root baseline or cleanup completion.'})
    # Bounded reviews are evidence/data, not extra worker instructions.
    review_files = {
        'inventory': [('review-inventory/POST-S2-INVENTORY-REVIEW.md','review.md'),
                      ('review-inventory/REVIEW-MANIFEST.json','manifest.json')],
        'workflow': [('review-workflow/review.md','review.md'),('review-workflow/review.json','review.json')],
        'inputs': [('final-review-r1/review.md','review.md'),('final-review-r1/review.json','review.json'),
                   ('final-review-r1/validation.json','validation.json'),
                   ('final-review-r1/validate_inputs_independent.py','validator.source.txt')],
    }
    for group, pairs in review_files.items():
        for source, target in pairs: copy(PREP/source, 'reviews/'+group+'/'+target)
    # Review output directories contain only the finite reviewed reports/harness data.
    for source_dir, prefix in [('final-review-pfr-r1','reviews/pfr'),('adapter-guards-r1','reviews/adapter-guards')]:
        folder = PREP/source_dir
        assert folder.is_dir(), 'Final reviewed tools/guard reports required: '+source_dir
        if source_dir == 'final-review-pfr-r1':
            files = sorted(p for p in folder.rglob('*') if p.is_file())
            assert files and all(p.suffix in ['.json','.md','.py','.txt'] for p in files)
        else:
            manifest = json.loads((folder/'DELIVERY-MANIFEST.json').read_text())
            files = [folder/'DELIVERY-MANIFEST.json']+[folder/r['path'] for r in manifest['files']]
            for row in manifest['files']:
                assert sha(folder/row['path'])==row['sha256']
        for file in files:
            relative = str(file.relative_to(folder))
            copy(file, prefix+'/'+relative)
    draft = PREP/'issue-draft-r2'
    brief = (draft/'brief.md').read_text()
    brief = re.sub(r'\*\*ISSUE CANDIDATE r2[^\n]+',
        '**ISSUED r1 — ready for user dispatch to one Claude session.** This is a cleanup assignment, not a completed fill or merge clearance. The source ancestor and worker choice below are fixed.', brief, count=1)
    brief = brief.replace('or the final separately pinned runtime-tool path', '`environment-tools/...`, `preship/...` or `reviews/...`')
    brief = brief.replace('Read the source checkout\'s `AGENTS.md`, `policy.md`, campaign `AGENTS.md`/maintainer handoff,',
        'Read the attached `methodology/source-AGENTS.md`, `methodology/policy.md`, current `methodology/campaign-AGENTS.md`/`methodology/MAINTAINER-HANDOFF.md`,')
    brief = brief.replace('### Required external PFR bootstrap — root must complete the operative route before issue', '### Required external PFR bootstrap')
    start = brief.index('**ROOT-FILL PLACEHOLDERS')
    end = brief.index('\nBaseline:', start)
    operative = '''**Operative route.** Verify `environment-tools/MANIFEST.json` (SHA-256 `TOOL_MANIFEST_SHA`) and follow the exact setup/31-check/PATH-boundary/probe commands in `environment-tools/RUNBOOK.md` (SHA-256 `RUNBOOK_SHA`). Its executable portable tools are `environment-tools/prepare_pfr.py` and `environment-tools/pfr_lean.py`; the normal-PATH metadata probe is `environment-tools/PFRIdentityProbe.source.txt`. Their exact byte counts/hashes are in that manifest and the issued `SHA256SUMS`. Use absolute attachment paths, an already working pinned real Lean binary and a fresh runtime directory; conflicting or escaping object paths are rejected. Review the supplied tool source before running it. This authorization is limited to this environment route, not historical scripts or new proof ownership.

**Maintainer validation limit:** the dependency/source/order/API/tool review passed statically, and the invocation guards were exercised without Lean. The maintainer's three native/cache launch attempts deferred with status75 before starting any cache, PFR compilation or owner probe because other chats had active Lean jobs. `preship/pfr/STATUS.json` records the exact observations; there is **no maintainer native PFR/owner-identity pass**. The successful selected existing TCSlib reuse probe in `preship/interface/` is a separate, limited result. No full-root/Checks cold baseline was performed or claimed pre-issue.

Checkpoint0 must reproduce the full narrowed cache/probe, 31-module external bootstrap and normal-PATH actual-header/constant-owner validation in the worker's own clone/tree before dependent checks. A zero private-name count, if encountered, validates no private-name sensitivity; retain its actual value. Preserve failures and the missing-product frontier. If this source-root/options route fails, report the exact evidence and escalation; do not repair package sources, introduce a locator workaround, run dependent checks or infer native success from static review. Genuine later resource/source errors retain E-RES/E-BASE treatment. Continue independent authorized work when it does not depend on the failed products.
'''
    operative = operative.replace('TOOL_MANIFEST_SHA',sha(tool_manifest)).replace('RUNBOOK_SHA',sha(DEST/'environment-tools/RUNBOOK.md'))
    brief = brief[:start]+operative+brief[end:]
    brief = brief[:brief.index('## Maintainer preparation checklist')]+'''**Ready to dispatch — one reviewed Claude cleanup job; checkpoint0 must freshly validate the external bootstrap before dependent checks.**
'''
    exceptions = (draft/'public-exceptions.md').read_text()
    exceptions = exceptions.replace('**ISSUE CANDIDATE r2 — paired with `brief.md`, not independently issued.**',
        '**ISSUED r1 — binding companion to `brief.md` for the same single Claude job.**')
    exceptions = exceptions.replace('**Not yet clear to merge — candidate exception contract awaiting final input/workflow review and user dispatch.**',
        '**Ready to dispatch — exhaustive cleanup exceptions; no worker completion or merge clearance.**')
    assert not re.search(r'PENDING_ROOT|ROOT-FILL|ISSUE CANDIDATE|Maintainer preparation checklist',brief+exceptions)
    (DEST/'brief.md').write_text(brief)
    (DEST/'public-exceptions.md').write_text(exceptions)
    (DEST/'ANCESTOR.txt').write_text(BASE+'\n')
    (DEST/'README.md').write_text('''# Cleanup part 2 — Claude dispatch pack r1

One coordinated cleanup job, selected by the user for **one Claude session**.
Read brief.md, public-exceptions.md and fill-environment-addendum.md first, verify
SHA256SUMS, then the named frozen inputs, environment runbook and methodology.
Source ancestor: **'''+BASE+'''**. The user's dispatch prompt supplies full immutable
records/exchange commit pins; no file asserts the hash of a commit containing itself.

The 45 frozen inputs retain 764 historical rows mapped to 509 current observation
keys, 97 consumer paths and 124 reader-only provider paths. Membership is not blanket
editing permission. The new canonical APIs are work targets; existing admissions,
security/algorithm contracts and all unlisted public bodies remain frozen.
No unmerged Gate06 dependency is introduced. Maintainer later reconciles overlaps
and opens a Lean PR for user approval.

The PFR environment route is concrete and statically/guard reviewed, with native
PFR validation **not run by the maintainer** because the shared host was busy.
Checkpoint0 on the worker's own host must validate it before dependent checks.
The separate existing-interface native probe passed with the limits in preship/.
No full library/root/Checks baseline or Rule10 clearance is asserted by this pack.
The old static supplement README's wrapper pass-through wording is superseded:
only its31 PFR checks use adapter PATH, and every probe/local/cache check uses
ordinary PATH. The final narrowed initial Mathlib union has389 roots; the original
375-root frozen input remains historical local-import coverage.

Push complete checkpoints/final only to **inbox/fills/cleanup-part2/** on
exchange/pass-shelat-ch5-8. Never push the source/fill/campaign branch. Use the
brief's complete patch-series/src/REPORT/evidence payload and preserve every other
campaign's files/index. The user dispatches this job and approves/merges the later PR.
No external job has been dispatched merely by staging this pack.

**Ready to dispatch — one Claude cleanup job, with fresh checkpoint0 environment validation required.**
''')
    # The pack manifest and outer checksum list have no self-hash cycle.
    files = [{'path':str(p.relative_to(DEST)), 'bytes':p.stat().st_size, 'sha256':sha(p)}
             for p in sorted(DEST.rglob('*')) if p.is_file()]
    manifest = DEST/'PACK-MANIFEST.json'
    dump(manifest, {'status':'ISSUED_READY_FOR_USER_DISPATCH_NOT_DISPATCHED', 'ancestor':BASE,
          'worker':'Claude', 'files':files, 'limitations':'See brief/preship: PFR native deferred; checkpoint0 mandatory; no full-root baseline or worker verification.'})
    all_files = sorted(p for p in DEST.rglob('*') if p.is_file())
    (DEST/'SHA256SUMS').write_text(''.join(sha(p)+'  '+str(p.relative_to(DEST))+'\n' for p in all_files))
    print(json.dumps({'pack':str(DEST), 'file_count':len(all_files)+1,
          'manifest_sha256':sha(manifest), 'sha256sums_sha256':sha(DEST/'SHA256SUMS'),
          'total_bytes':sum(p.stat().st_size for p in DEST.rglob('*') if p.is_file())},indent=2))


if __name__ == '__main__': main()
