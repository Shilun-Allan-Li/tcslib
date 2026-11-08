"""Prepare an independent records-only SG1 publication draft in a new temp directory.

No delivered code is imported/executed. Canonical/source/frozen files are read only.
"""
from pathlib import Path
import ast
import base64
import datetime
import difflib
import gzip
import hashlib
import io
import json
import os
import subprocess

R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
G=R/'campaign/gates/106-sg1-dedup'
F=G/'review/round3-final-packet'
PEER=G/'review/round3-final-packet-peer-review'
REL='campaign/gates/106-sg1-dedup/review/round3-publication-supplement'
OUT=Path('/private/tmp/sg1-publication-supplement-build-v3')
S=Path(os.environ['TCSLIB_SCRATCH'])
SOURCE=S/'wt-sg1'
NOW=datetime.datetime.now(datetime.timezone.utc).isoformat()
OUT.mkdir(exist_ok=False)

def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def save(n,data):(OUT/n).write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
def git(*args):return subprocess.run(['git','-C',str(SOURCE),*args],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True).stdout
def pin(p):
    b=p.read_bytes()
    return dict(bytes=len(b),sha256=sha(b))
def check_manifest(folder,expected):
    b=(folder/'MANIFEST.json').read_bytes();assert sha(b)==expected
    m=json.loads(b)
    rows=m['files'] if 'files' in m else m['artifacts']
    for row in rows:
        assert pin(folder/row['path'])==dict(bytes=row['bytes'],sha256=row['sha256']), row['path']
    return dict(path=str((folder/'MANIFEST.json').relative_to(R)),sha256=sha(b),payloads=len(rows))

frozen_checks=[check_manifest(F,'3bf0f54a07d9a4c96abc3a92fdbd007c593ab6788611e23fe26cd0cc438d5fed'),
               check_manifest(PEER,'a33f895768c48c265b8798c508a097f21b8bf87f2c1d9eec5d28d9cab89bdd82')]
head=git('rev-parse','HEAD').decode().strip()
base=git('rev-parse','3023dc1408c3d216fc07a7cbba9ae30135b861ed^{commit}').decode().strip()
git('cat-file','-e',head+'^{commit}');git('cat-file','-e',base+'^{commit}')
assert head=='79e7c63a6bfa5f002663924f5c7d4e72db705026' and not git('status','--porcelain=v1')
apihead=git('rev-parse','f1ca767a10551960faf36ad9c8ff17bea3a2d88c^{commit}').decode().strip()
git('cat-file','-e',apihead+'^{commit}')
records_observed=subprocess.run(['git','-C',str(R),'rev-parse','HEAD'],stdout=subprocess.PIPE,check=True).stdout.decode().strip()

helper=[]
for name in ['graph.py','mkdownmulti.py','mkreplay.py']:
    repo=R/'devtools/seyoon'/name;actual=S/'tools'/name
    b=repo.read_bytes();assert b==actual.read_bytes()==git('show',head+':devtools/seyoon/'+name)
    tree=ast.parse(b.decode());imports=[]
    for node in ast.walk(tree):
        if isinstance(node,ast.Import):imports.extend(x.name for x in node.names)
        elif isinstance(node,ast.ImportFrom):imports.append(node.module)
    helper.append(dict(path=str(repo.relative_to(R)),actual_generation_copy=str(actual),**pin(repo),
        source_commit=head,source_blob=git('rev-parse',head+':devtools/seyoon/'+name).decode().strip(),
        imports=sorted(set(imports)),actual_repo_and_pinned_source_bytes_exact=True))
graph=helper[0];assert graph['imports']==['os','sys']
assert helper[1]['imports']==['graph','os','sys'] and helper[2]['imports']==['os','sys']
(OUT/'graph.py.txt').write_bytes((R/'devtools/seyoon/graph.py').read_bytes())
actual_mknext=S/'tools/mk-next.sh';included_mknext=R/'campaign/status/2026-11-06-mac-bootstrap/mk-next-codex.sh'
assert actual_mknext.read_bytes()==included_mknext.read_bytes()
save('helper-provenance.json',dict(utc=NOW,result='PQ1 exact helper supplied; transitive import closes in stdlib',
    graph_copy=str(Path(REL)/'graph.py.txt'),original_path='devtools/seyoon/graph.py',helpers=helper,
    actual_mknext=dict(actual=str(actual_mknext),included=str(included_mknext.relative_to(R)),**pin(actual_mknext),exact=True),
    no_delivered_helper_execution=True,no_native_or_snapshot_operation=True))

old_sections=(F/'BUNDLE-FILES-candidate.txt').read_text().splitlines()
assert len(old_sections)==len(set(old_sections))==1539
encoding=load(F/'encoding-receipt.json')
aliases={}
for x in encoding['transforms']:
    raw=(R/x['original']['path']).read_bytes();encoded=(R/x['encoding_path']).read_bytes()
    packed=base64.b64decode(b''.join(encoded.split()),validate=True)
    assert gzip.decompress(packed)==raw
    assert (len(raw),sha(raw))==(x['original']['bytes'],x['original']['sha256'])
    assert (len(packed),sha(packed))==(x['gzip_bytes'],x['gzip_sha256'])
    assert (len(encoded),sha(encoded))==(x['encoded_utf8_bytes'],x['encoded_utf8_sha256'])
    buffer=io.BytesIO()
    with gzip.GzipFile(fileobj=buffer,filename='',mode='wb',compresslevel=9,mtime=0) as stream:stream.write(raw)
    assert buffer.getvalue()==packed
    aliases[x['original']['path']]=x['encoding_path']
assert len(aliases)==40 and len(set(aliases.values()))==31
for x in encoding['binary_gzip_equivalents']:
    assert (R/x['path']).read_bytes()==base64.b64decode((R/x['represented_by']).read_bytes())
original=load(F/'original-inputs.json')
mutable={'campaign/gates/106-sg1-dedup/STATUS.md','campaign/gates/106-sg1-dedup/resolutions-r2.md',
    'campaign/gates/119-mig1-followup-api/resolutions.md','campaign/maintainer/HANDOFF.md','campaign/maintainer/START-HERE.md','campaign/duplication-ledger.md',
    'campaign/backlog.md'}
drift=[]
for row in original['files']:
    current=pin(R/row['path'])
    if current!=dict(bytes=row['bytes'],sha256=row['sha256']):
        assert row['path'] in mutable, row['path']
        drift.append(dict(path=row['path'],frozen=dict(bytes=row['bytes'],sha256=row['sha256']),current=current,
                          classification='Mutable publication/status chronology; original receipt remains historical'))
save('frozen-input-verification.json',dict(utc=NOW,frozen_manifests=frozen_checks,original_text_inputs=len(original['files']),
    original_unchanged=len(original['files'])-len(drift),mutable_context_drift_count=len(drift),
    immutable_original_drift=[],all40_aliases_preserved_and_roundtripped=True,distinct_encoded_sections=31,
    all3_binary_companions_exact=True,source_head=head,source_clean=True,no_frozen_directory_edited=True))

api=R/'campaign/gates/119-mig1-followup-api';closure=load(api/'closure.json')
assert closure['state']=='CLOSED' and closure['verdict']=='PASS' and closure['notes']==17
assert closure['blockers']==closure['majors']==closure['minors']==0 and closure['clear_to_merge']
assert closure['source']==apihead
assert pin(api/'findings-r2.md')['sha256']==closure['findings_sha256']
api_review=api/'review/round2-return-review'
check=check_manifest(api_review,closure['review_manifest_sha256'])
api_files=[api/x for x in ['STATUS.md','closure.json','findings-r2.md','findings-r2-receipt.json','resolutions.md']]
for folder in ['round2-closure','round2-return-review']:
    api_files.extend(p for p in sorted((api/'review'/folder).rglob('*')) if p.is_file())
api_files=sorted(set(api_files))
readiness_folder=R/'campaign/status/2026-11-08-current-proof-readiness'
readiness_files=sorted(p for p in readiness_folder.rglob('*') if p.is_file())
for row in load(readiness_folder/'MANIFEST.json')['files']:
    assert pin(readiness_folder/row['path'])==dict(bytes=row['bytes'],sha256=row['sha256'])
current_readiness=load(readiness_folder/'readiness.json')
sg1_readiness=next(x for x in current_readiness['results'] if x['pr']==215)
assert sg1_readiness['source']==head and sg1_readiness['comparison_lean_base']==base
assert sg1_readiness['merge_tree_exit']==0 and sg1_readiness['merged_Lean_equals_passed_source']
assert sg1_readiness['github_mergeable'] is None and sg1_readiness['github_mergeable_state']=='unknown'
save('context-rebinding.json',dict(utc=NOW,observed_records_commit=records_observed,
    observed_commit_is_not_final_publication_pin=True,source_head=head,comparison_base=base,
    frozen_receipt_context_changes=drift,
    gate119=dict(source=apihead,state='CLOSED PASS0/0/0/17',clear_to_merge=True,
        merged=False,still_absent_and_unused_by_SG1=True,
        authority='Root current instruction plus closure.json/STATUS.md; no GitHub request or new native run here',
        closure_record=str((api/'closure.json').relative_to(R)),review_manifest_check=check,
        scope='Closure/current-status context only; does not expand SG1 audit into API119 source/replay re-audit',
        complete_context_folders=[str((api/'review'/x).relative_to(R)) for x in ['round2-closure','round2-return-review']],
        context_files=[dict(path=str(p.relative_to(R)),**pin(p)) for p in api_files]),
    current_proof_readiness=dict(folder=str(readiness_folder.relative_to(R)),complete_files=len(readiness_files),
        all_manifest_payloads_exact=True,scope='Prospective merged Lean/source equality context only; includes separate PR235 context without expanding SG1 audit.',
        SG1_status='Not yet clear to merge: external audit open',github_mergeability='null/unknown; no clear-to-merge inference',
        files=[dict(path=str(p.relative_to(R)),**pin(p)) for p in readiness_files]),
    root_rebind_required='After adopting canonical draft, recapture all mutable final input bytes at final records pin; preserve frozen earlier receipts rather than overwrite them.'))

candidate=(F/'candidate-pack-r3.md').read_text()
old_api='''The canonical proposed exists_first_entry_of_fixed is still on UNMERGED prerequisite#234;
it is not present or used in this SG1 source, and this PR gains no dependency on it. The
five current Hardness members are clFirst, clBank_first, clCopy_first, clRow_first and'''
new_api='''**Clear to merge: #234 — gate119 CLOSED PASS0/0/0/17; Seyoon has not merged it.**
The canonical proposed exists_first_entry_of_fixed remains on UNMERGED prerequisite#234,
source f1ca767a10551960faf36ad9c8ff17bea3a2d88c. It is not present or used in this SG1 source,
and this PR gains no dependency on it. Current closure/status/findings/dispositions and
complete closure/return-review context are supplied as records, not a new SG1 native run
or an instruction to re-audit API119. Closure does not retire FE-LIVE-1 implementation debt.
The five current Hardness members are clFirst, clBank_first, clCopy_first, clRow_first and'''
assert candidate.count(old_api)==1
draft=candidate.replace(old_api,new_api)
anchor='''The candidate input list also supplies every cited standard, all originalR1/R2 findings and
dispositions, complete current/historical source populations, actual raw controls and failures,
all compiled output encodings and by-kind decision evidence. No folder listing is capped.'''
replacement='''The publication input draft retains EVERY original1539 candidate section, all40→31 lossless
aliases and all50 current plaintext source captures, and adds the complete frozen independent
peer review plus review/round3-publication-supplement/. Its exact expanded count belongs in
the finalized prologue. The canonical pack is the leading additional section; the original
candidate pack/list/receipts stay historical sections. The missing replay-generator dependency
devtools/seyoon/graph.py is supplied byte-exact, also as inert graph.py.txt in the supplement,
with source/blob/SHA256 and actual-generation-copy provenance; graph imports only os/sys.
This resolves peer PQ1 in the publication draft without altering any frozen packet/review.
The fresh external-input inventory and context-rebinding receipt distinguish current mutable
status records from older capture pins. Root still binds final adopted bytes at the final
records commit. All cited standards, originalR1/R2 findings/dispositions, complete historical
source populations, raw controls/failures, compiled encodings and decision evidence remain.
No folder listing is capped. Peer review is packet QA, not the external gate verdict.'''
assert draft.count(anchor)==1
draft=draft.replace(anchor,replacement)
(OUT/'canonical-pack-r3-draft.md').write_text(draft)
canonical=G/'pack-r3.md';before=canonical.read_text()
patch=''.join(difflib.unified_diff(before.splitlines(keepends=True),draft.splitlines(keepends=True),
    fromfile='a/campaign/gates/106-sg1-dedup/pack-r3.md',tofile='b/campaign/gates/106-sg1-dedup/pack-r3.md'))
(OUT/'canonical-pack-r3.patch').write_text(patch)
save('publication-changes.json',dict(utc=NOW,canonical_path=str(canonical.relative_to(R)),
    canonical_current=pin(canonical),candidate_basis=pin(F/'candidate-pack-r3.md'),
    proposed_canonical=pin(OUT/'canonical-pack-r3-draft.md'),exact_candidate_replacements=2,
    changes=['Adopt final79 candidate rather than staleD0 canonical draft, preserving all substantive source/evidence claims.',
             'State gate119CLOSED/#234Clear but stillunmerged/unused; preserve FE-LIVE scheduled cleanup.',
             'Bind PQ1 graph dependency fix, full frozen peer review and strict input-list superset through supplement.'],
    unchanged_claims=['Source79/base3023','16+1 proof repoints and precisely approved two Hardness imports',
        'MSG5→6→7 complete-snapshot lineage','Current25 screen metrics/deltas','Full compiled7101→7063/public1351/simp168/root43+93AX',
        'Seven SG1 kinds separate from FE-LIVE; named54/544 union only; unacknowledged clNative_image residual'],
    remaining_root_actions=['Adopt canonical-pack-r3-draft.md at canonical pack-r3.md after checking patch/basis hash.',
        'Adopt BUNDLE-FILES-r3-draft.txt as final publication list; original1539 sections remain.',
        'Finalize canonical ledger/status chronology, finalrecords linkage, renderedbundle bytes/SHA/section count and exchange/prompt.',
        'Recheck #234 merger state immediately before final publication and refresh only current context if it changes.'],
    no_source_or_canonical_changes_performed=True))

readme='''# SG1 round3 publication supplement — PQ1 resolved in draft

**Not yet clear to merge: #215 — selected external round3 is still open.**

This new folder supplies the exact missing graph helper and a complete publication draft.
The frozen candidate and independent peer-review folders remain unchanged. No source,
canonical pack/list, ledger or status record was edited, and no readiness/dispatch/merge
authority is exercised here.

`graph.py.txt` is byte-exact to `devtools/seyoon/graph.py` and the actual scratch generation
copy. SHA256 `c4c1aa599a091c88f77062fd2fca4482ed8017e683819a650e343760ac78d72c`,4784bytes;
the only imports are standard-library os/sys. `helper-provenance.json` also binds the exact
mkdownmulti/mkreplay source blobs and actual Codex mk-next variant. Original root graph.py
and the inert copy are both in the draft bundle list. This closes peer PQ1's missing-input
condition in the prepared draft; root must still render/publish the section.

`BUNDLE-FILES-r3-draft.txt` is a strict superset of every1539 frozen candidate section and
retains their original relative order. All40→31 aliases and all50 current plaintext source
captures remain. It adds canonical pack-r3.md as the leading section, all7 frozen peer-review
files, the exact graph helper, every file in this new folder, and current API119 closure
context without a folder cap. No original input is removed/re-encoded/substituted. The only
prospective path-byte override in QA is canonical pack-r3.md, whose current staleD0 text is
replaced by `canonical-pack-r3-draft.md` when root adopts it. Both current and prospective
payload byte counts are reported; final rendered-bundle verification remains root-owned.

`canonical-pack-r3.patch` is a concrete unified diff against the observed canonical pack.
`publication-changes.json` pins old canonical/candidate/proposed bytes. Root can adopt the
proposed file after checking that basis. The source/evidence metrics remain final79/3023;
current wording adds gate119CLOSED PASS0/0/0/17 and **Clear to merge: #234**, still UNMERGED
and unused by SG1. This closure context does not import an API or authorize an SG1 replay
claim, clear #215, or retire FE-LIVE debt. The complete round2-closure/return-review folders,
closure/status/findings/receipt/resolutions records support that status; this does not ask
the SG1 auditor to recursively re-audit the API119 packet.

The complete10-file `campaign/status/2026-11-08-current-proof-readiness/` folder is also
supplied as current context. Its prospective merges preserve the passed source trees;
GitHub mergeability is null/unknown. It does not clear #215 or #235: their external audits
remain open, and no new replay/source check is claimed here.

`external-input-inventory.json` freshly pins every path outside this new folder at preparation
time, with the canonical-pack draft substitution explicitly marked. `context-rebinding.json`
records permitted mutable chronology drift from the old frozen inventory. Earlier receipts
are historical; they are not silently edited or asserted to hash the new status prose.
Root must rebind final adopted current records after its final records commit. No record
needs to contain the hash of its own not-yet-created commit.

`QA.json` and `MANIFEST.json` check the strict superset, complete frozen peer folder, all
new outputs, UTF8, aliases, graph provenance, closure receipts and payload-size bound.
`build-supplement.py` is the own standard-library draft builder retained as data; no supplied
script was executed. No Lean, screen, snapshot/cache operation, Git mutation, commit/push,
external dispatch, or source/canonical/frozen write occurred. Root owns final readiness,
ledger/status, staging, exchange publication and prompt.
'''
(OUT/'README.md').write_text(readme)
(OUT/'build-supplement.py').write_bytes(Path(__file__).read_bytes())
save('preparation-history.json',dict(first_attempt=dict(output='/private/tmp/sg1-publication-supplement-build',
    outcome='Own data-only builder stopped on START-HERE.md chronology drift before list/pack publication outputs',
    reason='Parent updated current gate119 closure paragraph while final publication preparation progressed',
    resolution='Read exact current paragraph, classify it with permitted mutable chronology, regenerate in new temp directory',
    only_partial_outputs=['graph.py.txt','helper-provenance.json'],no_native_or_canonical_or_frozen_write=True),
    second_attempt=dict(output='/private/tmp/sg1-publication-supplement-build-v2',
        outcome='Own data-only verifier stopped before final outputs on API119 manifest schema key',
        resolution='Accept actual artifacts manifest field as well as files; verify exact same22 payloads',
        no_native_or_canonical_or_frozen_write=True),
    current_attempt='Fresh v3 output with explicit current-context rebind and exact manifest schema; all frozen inputs remain validated'))

own_names=['README.md','graph.py.txt','helper-provenance.json','frozen-input-verification.json',
    'context-rebinding.json','canonical-pack-r3-draft.md','canonical-pack-r3.patch','publication-changes.json',
    'build-supplement.py','preparation-history.json','external-input-inventory.json','BUNDLE-FILES-r3-draft.txt','QA.json','MANIFEST.json']
new_external=[str(p.relative_to(R)) for p in sorted(PEER.rglob('*')) if p.is_file()]
new_external+=['devtools/seyoon/graph.py']+[str(p.relative_to(R)) for p in api_files]
new_external += [str(p.relative_to(R)) for p in readiness_files]
sections=[str(canonical.relative_to(R))]+old_sections
for p in new_external+[str(Path(REL)/n) for n in own_names]:
    if p not in sections:sections.append(p)
assert len(sections)==len(set(sections)) and set(old_sections)<=set(sections)
assert [x for x in sections if x in set(old_sections)]==old_sections
assert all(str(p.relative_to(R)) in sections for p in PEER.rglob('*') if p.is_file())
assert all(str(p.relative_to(R)) in sections for p in api_files)
assert all(str(p.relative_to(R)) in sections for p in readiness_files)
assert set(aliases.values())<=set(sections)
for p in (G/'review/round3-current-source-screen25-final79/inputs').rglob('*.lean.txt'):
    assert str(p.relative_to(R)) in sections
(OUT/'BUNDLE-FILES-r3-draft.txt').write_text('\n'.join(sections)+'\n')

inventory=[]
for rel in sections:
    if rel.startswith(REL+'/'):continue
    p=R/rel;b=p.read_bytes();b.decode('utf-8')
    row=dict(path=rel,**pin(p))
    if p==canonical:
        row=dict(path=rel,**pin(OUT/'canonical-pack-r3-draft.md'),prospective=True,
                 proposed_from=str(Path(REL)/'canonical-pack-r3-draft.md'),observed_current=pin(p))
    inventory.append(row)
save('external-input-inventory.json',dict(utc=NOW,source_head=head,observed_records_commit=records_observed,
    final_records_pin_not_claimed=True,scope='All draft paths outside this new supplement; exactly one explicit prospective canonical-pack substitution',
    files=inventory))

qa=dict(utc=NOW,result='PASS publication draft complete; PQ1 graph dependency included; root adoption/render/publication pending',
    source_head=head,source_clean=True,comparison_base=base,
    canonical_files_written=False,frozen_manifests_unchanged=frozen_checks,
    old_sections=1539,new_sections=len(sections),all1539_preserved_in_order=True,
    source50_plaintext_preserved=True,all40_original_aliases_and31_encoded_sections_preserved=True,
    exact_graph_original_and_copy_included=True,graph_imports_stdlib_only=True,
    peer_review_complete_files=sum(p.is_file() for p in PEER.rglob('*')),
    gate119_closure_context_complete_files=len(api_files),gate119_state='CLOSED PASS0/0/0/17; #234 Clear but UNMERGED/unused bySG1',
    current_proof_readiness_complete_files=len(readiness_files),readiness_does_not_infer_mergeability_or_gate_clearance=True,
    all_new_supplement_outputs_in_list=True,external_inventory_rows=len(inventory),
    draft_list_sha256=sha((OUT/'BUNDLE-FILES-r3-draft.txt').read_bytes()),
    mutable_context_drift_count=len(drift),immutable_drift=[],
    current_payload_utf8_bytes=0,prospective_payload_utf8_bytes=0,hosting_limit_bytes=100*1024*1024,
    payload_under_limit=True,final_rendered_bytes_and_records_pin_root_owned=True,
    no_Lean_screen_snapshot_cache_Git_or_canonical_mutation=True)

def payload(prospective):
    total=0
    for rel in sections:
        if rel.startswith(REL+'/'):p=OUT/Path(rel).name
        elif prospective and rel==str(canonical.relative_to(R)):p=OUT/'canonical-pack-r3-draft.md'
        else:p=R/rel
        b=p.read_bytes();b.decode('utf-8');total+=len(b)
    return total

last=None
for _ in range(10):
    save('QA.json',qa)
    rows=[dict(path=f.name,**pin(f)) for f in sorted(OUT.iterdir()) if f.is_file() and f.name!='MANIFEST.json']
    save('MANIFEST.json',dict(status='Frozen publication supplement draft; no canonical adoption/publication',utc=NOW,
        source_head=head,candidate_manifest_sha256=frozen_checks[0]['sha256'],peer_manifest_sha256=frozen_checks[1]['sha256'],files=rows))
    sizes=(payload(False),payload(True))
    if sizes==last:break
    qa['current_payload_utf8_bytes'],qa['prospective_payload_utf8_bytes']=sizes;last=sizes
else:raise AssertionError('Payload length accounting did not stabilize')
assert payload(False)==qa['current_payload_utf8_bytes'] and payload(True)==qa['prospective_payload_utf8_bytes']
assert max(payload(False),payload(True))<qa['hosting_limit_bytes']
assert sorted(f.name for f in OUT.iterdir())==sorted(own_names)
for row in load(OUT/'MANIFEST.json')['files']:assert pin(OUT/row['path'])==dict(bytes=row['bytes'],sha256=row['sha256'])
assert pin(F/'MANIFEST.json')['sha256']==frozen_checks[0]['sha256'] and pin(PEER/'MANIFEST.json')['sha256']==frozen_checks[1]['sha256']
assert not git('status','--porcelain=v1') and git('rev-parse','HEAD').decode().strip()==head
print(json.dumps(dict(output=str(OUT),target=REL,files=len(own_names),sections=len(sections),
    candidate1539_preserved=True,peer7_preserved=True,aliases40_to31_unchanged=True,
    current_payload_bytes=payload(False),prospective_payload_bytes=payload(True),
    manifest_sha256=sha((OUT/'MANIFEST.json').read_bytes()),canonical_draft_sha256=sha(draft.encode()),
    PQ1='resolved in prepared draft; root final adoption/render/publish pending'),indent=2))
