"""Prepare F6 final publication as data, with the stage tool's exact mixed-pin rule.
No supplied script, Lean, screen, source/canonical/frozen mutation, or Git write.
"""
from pathlib import Path
import ast, base64, codecs, datetime, difflib, gzip, hashlib, io, json, os, re, subprocess

R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
F=R/'campaign/fills/f6';L=F/'landing';G=R/'campaign/gates/120-f6-space-universal'
P=G/'review/packet-draft';ROOTD=G/'review/publication-packet'
REL='campaign/gates/120-f6-space-universal/review/final-publication-preparation'
OUT=Path('/private/tmp/f6-final-publication-preparation-v1')
HEAD='0d0950caeb39300b5cc9bf41e5f07392fb26d3e5'
BASE='3023dc1408c3d216fc07a7cbba9ae30135b861ed'
IREC='f41bdaea207724606d8934bfc2c9a823c5dd1e2f'
EXCH='2adb80788611696d2cad6f907285c0c5a197ae09'
NOW=datetime.datetime.now(datetime.timezone.utc).isoformat()
OUT.mkdir(exist_ok=False)
sha=lambda b:hashlib.sha256(b).hexdigest()
load=lambda p:json.loads(p.read_text())
def save(n,d):
    p=OUT/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def git(*args):return subprocess.run(['git','-C',str(R),*args],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE).stdout
def pin(b):return dict(bytes=len(b),sha256=sha(b))
def filepin(p):return pin(p.read_bytes())
for rev in [HEAD,BASE,IREC,EXCH]:
    assert git('rev-parse',rev+'^{commit}').decode().strip()==rev;git('cat-file','-e',rev+'^{commit}')
REC=git('rev-parse','HEAD').decode().strip()
source=git('show',HEAD+':TCSlib/Complexity/SpaceComplexity/Hierarchy.lean')
assert sha(source)=='550c59f38193d19156d215c6e7d6ef5f005a11a5bd3182c6cc443ba25790b8a3'
assert git('diff','--name-only',BASE,HEAD,'--','*.lean').decode().splitlines()==['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean']
def mixed(rel):
    return git('show',HEAD+':'+rel) if rel.startswith('TCSlib/') else (R/rel).read_bytes()

expected={
 str(P.relative_to(R)):'',
 'campaign/fills/f6/landing/compiled-accounting-final':'0c8d3487e95c62731d750f2b91f1a93314b64861bffced766d5389885e2faad9',
 'campaign/fills/f6/landing/source-screen23-resumed':'9412b0d8bcdbb4dd28583069c78100e22f7abf69316ec2a5c6292364e815329a',
 'campaign/fills/f6/landing/source-screen23-resumed/final23-current':'2b0c6cf93595fef48fe5bc9eac9ee911e521f309bb4ed831aa4256ad34062f2c',
 'campaign/fills/f6/landing/seam-step-repoint-applied':'318e85633bb50630d9c6f633f6907eb74da5faa7e3f490427c24e60cb2a99671',
 'campaign/fills/f6/landing/seam-step-repoint-preflight':'7fcf7920c7d3922804ef747039b2389065b920e0d2a481e892584679a753ce2c',
 'campaign/fills/f6/landing/replay-mf62':'27ac72195ded51b9d64ed1cebe57b9d13bdb6394a9cf11fa4678a3e6b7f7b586'}
frozen=[]
for rel,digest in expected.items():
    p=R/rel;b=(p/'MANIFEST.json').read_bytes()
    if digest:assert sha(b)==digest
    m=json.loads(b);rows=m.get('files',m.get('artifacts',[]));assert rows
    for row in rows:assert filepin(p/row['path'])==dict(bytes=row['bytes'],sha256=row['sha256']),str(p/row['path'])
    frozen.append(dict(folder=rel,manifest_sha256=sha(b),verified_payloads=len(rows),physical_files=sum(x.is_file() for x in p.rglob('*'))))
ROOTBYTES=(ROOTD/'pack.candidate.md').read_bytes()
assert sha(ROOTBYTES)=='8e7c9efa75eb97d065c56360c69ccb083212c150e9c8086bd6fe8435e2a5d110'

old815=(P/'BUNDLE-FILES.candidate.txt').read_text().splitlines()
issued=(P/'BUNDLE-FILES.issued-immutable.txt').read_text().splitlines()
assert len(old815)==len(set(old815))==815 and len(issued)==624 and old815[:624]==issued
oldpart=load(P/'issued-to-audit-input-partition.json');assert [x['path'] for x in oldpart['files']]==issued
parts=[];partition=[]
for row in oldpart['files']:
    rel=row['path'];rev=BASE if rel.startswith('TCSlib/') else IREC
    assert row['issued_pin']==rev
    old=git('show',rev+':'+rel);assert pin(old)==dict(bytes=row['issued_bytes'],sha256=row['issued_sha256'])
    text=old.decode('utf-8');text+= '' if text.endswith('\n') else '\n'
    if rel.endswith(('.lean','.py')):text='```\n'+text+'```\n'
    parts.append('## ===== '+rel+' =====\n\n'+text)
    now=mixed(rel);now.decode('utf-8')
    item=dict(path=rel,issued_pin=rev,issued=pin(old),current=pin(now),current_binding='source:'+HEAD if rel.startswith('TCSlib/') else 'records candidate, final pin root-owned',status='unchanged' if old==now else 'intentional source landing' if rel.startswith('TCSlib/') else 'current records chronology')
    if old!=now:
        cap='historical-issued-current-partition/'+rel+'.txt';p=OUT/cap;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(old)
        item['full_issued_capture']=str(Path(REL)/cap)
    partition.append(item)
rebuilt='\n'.join(parts).encode()
original=git('show',EXCH+':arora-barak-ch3-4/outbox/fills/f6-space-universal/f6-space-universal-bundle.md')
assert rebuilt==original and len(original)==8707327 and sha(original)=='8fa482702846898f7fa04c4e1b0aa012300b4febaa6385ee8caa869cf14740be'
save('issued-to-current-partition.json',dict(utc=NOW,issued_source=BASE,issued_records=IREC,issued_exchange=EXCH,
    issued_sections=624,issued_bundle=pin(original),independently_rebuilt_exact=True,
    build_rule='All TCSlib/ at Lean source pin; every other path at records pin. Own renderer matches actual mkbundle-mixed formatting, no supplied code executed.',
    current_source=HEAD,current_records_observed_not_final=REC,all624_files=partition))

# Whole uncapped F6 material, all old gate drafts, and the current prerequisite context.
scope=set(old815)
for root in [F,G]:
    for p in sorted(root.rglob('*')):
        if p.is_file() and not str(p.relative_to(R)).startswith(REL+'/'):scope.add(str(p.relative_to(R)))
api=R/'campaign/gates/119-mig1-followup-api';closure=load(api/'closure.json')
assert closure['state']=='CLOSED' and closure['clear_to_merge'] and closure['notes']==17
api_files=[api/x for x in ['STATUS.md','closure.json','findings-r2.md','findings-r2-receipt.json','resolutions.md']]
for name in ['round2-closure','round2-return-review']:
    api_files.extend(p for p in sorted((api/'review'/name).rglob('*')) if p.is_file())
readiness=R/'campaign/status/2026-11-08-current-proof-readiness'
context_files=sorted(set(api_files+[p for p in readiness.rglob('*') if p.is_file()]))
scope.update(str(p.relative_to(R)) for p in context_files)
tools=['devtools/seyoon/graph.py','devtools/seyoon/mkdownmulti.py','devtools/seyoon/mkreplay.py',
 'devtools/seyoon/mkbundle-mixed.py','devtools/seyoon/verifybundle.py','devtools/seyoon/stage.sh',
 'devtools/seyoon/leanelab.sh','devtools/seyoon/leanelab-o.sh','devtools/seyoon/staticsorry.py',
 'devtools/seyoon/scratch-api/slotrun.sh','devtools/seyoon/declfreeze.py','devtools/seyoon/pairdiff.py',
 'scripts/copy-text-screen-v3.py','scripts/style_lint.py','scripts/campaign_style_lint.py']
scope.update(tools)
helper=[]
for rel in tools:
    b=(R/rel).read_bytes();modules=[]
    if rel.endswith('.py'):
        for n in ast.walk(ast.parse(b.decode())):
            if isinstance(n,ast.Import):modules.extend(x.name for x in n.names)
            elif isinstance(n,ast.ImportFrom):modules.append(n.module)
    helper.append(dict(path=rel,**pin(b),imports=sorted(set(modules))))
for name in ['graph.py','mkdownmulti.py','mkreplay.py']:
    b=(R/'devtools/seyoon'/name).read_bytes()
    assert b==git('show',HEAD+':devtools/seyoon/'+name)==(L/'replay-mf62'/(name+'.txt')).read_bytes()
(OUT/'graph.py.txt').write_bytes((R/'devtools/seyoon/graph.py').read_bytes())
save('helper-provenance.json',dict(utc=NOW,source=HEAD,helpers=helper,
    exact_replay_generator_copies=['graph.py','mkdownmulti.py','mkreplay.py'],
    transitive_dependency='mkdownmulti→graph→stdlib(os,sys); exact original graph.py and inert copy included',
    mixed_pin_rule='TCSlib/ only from source0d; all other paths from records candidate, matching mkbundle-mixed.py',
    supplied_code_executed=False))

# Existing complete binary aliases are preserved byte-for-byte; new gzip companions are explicit.
binary=[];binary_map={}
for row in load(P/'utf8-archive-roundtrips.json')['archives']:
    rel=row['original'];alias=row['UTF8_representation'];raw=(R/rel).read_bytes();encoded=(R/alias).read_bytes()
    assert pin(raw)==dict(bytes=row['original_bytes'],sha256=row['original_sha256'])
    assert pin(encoded)==dict(bytes=row['encoded_bytes'],sha256=row['encoded_sha256'])
    assert base64.b64decode(b''.join(encoded.split()),validate=True)==raw
    binary_map[rel]=alias;binary.append(dict(original=rel,raw=pin(raw),representation=alias,encoded=pin(encoded),kind='preserved existing binary alias',roundtrip=True))
for rel in sorted(scope):
    if rel in binary_map:continue
    p=R/rel
    if p.suffix=='.gz':
        alias=rel+'.base64.txt';assert (R/alias).is_file(),rel
        raw=p.read_bytes();encoded=(R/alias).read_bytes()
        assert base64.b64decode(b''.join(encoded.split()),validate=True)==raw
        binary_map[rel]=alias;binary.append(dict(original=rel,raw=pin(raw),representation=alias,encoded=pin(encoded),kind='new frozen gzip companion',roundtrip=True));scope.add(alias)
assert len(binary)==18 and all(x['representation'] in scope for x in binary)
# Stream the optional diagnostic only as bytes/UTF8, without retaining or interpreting its proof values.
diag=load(L/'compiled-accounting/Fintype-uses-v2-run.json');h=hashlib.sha256();count=0;decoder=codecs.getincrementaldecoder('utf-8')()
with gzip.open(L/'compiled-accounting/Fintype-uses-v2.out.gz','rb') as stream:
    while True:
        chunk=stream.read(8*1024*1024)
        if not chunk:break
        h.update(chunk);count+=len(chunk);decoder.decode(chunk)
decoder.decode(b'',final=True)
assert count==diag['raw_stdout_stderr_bytes']==980644140 and h.hexdigest()==diag['raw_stdout_stderr_sha256']
save('binary-alias-receipt.json',dict(utc=NOW,archives=binary,preserved_existing_aliases=10,new_frozen_binary_aliases=8,
    optional_diagnostic=dict(raw_bytes=count,raw_sha256=h.hexdigest(),complete_streamed_UTF8_gzip_validation=True,
        semantic_review=False,required_for_primary_census=False,original_gzip=pin((L/'compiled-accounting/Fintype-uses-v2.out.gz').read_bytes())),
    no_binary_or_native_byte_omitted=True))

encoded_map={};transforms=[];dedup={}
protected=set(issued)|{x['representation'] for x in binary}
for rel in sorted(scope):
    if rel in binary_map or rel in protected:continue
    p=R/rel;size=p.stat().st_size
    if not((p.suffix=='.json' and size>250000) or (rel.endswith('.tar.base64.txt') and size>250000)):continue
    raw=mixed(rel);raw.decode('utf-8');key=sha(raw)
    if key not in dedup:
        buf=io.BytesIO()
        with gzip.GzipFile(fileobj=buf,mode='wb',filename='',compresslevel=9,mtime=0) as stream:stream.write(raw)
        packed=buf.getvalue();encoded=base64.encodebytes(packed)
        name=f'encodings/{len(dedup)+1:03d}-{p.name}.gz.base64.txt';q=OUT/name;q.parent.mkdir(exist_ok=True);q.write_bytes(encoded)
        dedup[key]=(str(Path(REL)/name),packed,encoded)
    alias,packed,encoded=dedup[key]
    assert gzip.decompress(base64.b64decode(encoded))==raw
    encoded_map[rel]=alias
    transforms.append(dict(original=rel,raw=pin(raw),representation=alias,gzip=pin(packed),encoded=pin(encoded),
        deterministic='gzip9,mtime0,empty filename; Base64ASCII',stdlib_roundtrip=True,source_capture=False))
save('UTF8-substitution-receipt.json',dict(utc=NOW,substituted_originals=len(transforms),distinct_encoded_sections=len(dedup),
    transforms=transforms,original_files_unchanged=True,all_existing10_archive_aliases_preserved=True,
    original624_prefix_untouched=True,full815_scope_preserved_through_literal_or_lossless_representation=True,
    no_source_capture_raw_screen_or_control_output_encoded=True,decode_as_data_never_execute=True))

M=L/'compiled-accounting-final';screen=L/'source-screen23-resumed/final23-current'
summary=load(M/'summary.json');controls=load(M/'scoped-seals-final/control-verification.json');pd=load(screen/'pair-delta.json')
assert summary['endpoints']['Head']['all']==193 and summary['all_current_owned_AXIOMS_standard_or_subset']
assert controls['scopes']==19 and controls['positive_kernel_checked_identities']==controls['expected_negative_identities']==72
assert (pd['base']['declarations'],pd['head']['declarations'],pd['base']['candidates'],pd['head']['candidates'],pd['base']['reproduced_chars'],pd['head']['reproduced_chars'])==(1113,1124,647,648,172081,172243)
assert len(pd['new'])==1 and not pd['gone'] and not pd['changed_measurements']
draft=ROOTBYTES.decode();replacements=[]
def replace(old,new):
    global draft
    assert draft.count(old)==1,old
    draft=draft.replace(old,new);replacements.append(dict(before=old,after=new))
replace('`seamCompTM_run_ofCfg` and `seamCompTM_firstReturn_ofCfg`.', '`seamCompTM_step` (the current exact seam forwarding contract).')
replace('CURRENT_SEALS_FINAL_RECEIPTS_PENDING','''**Fresh current0d seals/controls:** compiled-accounting-final supplies complete actual source
native/19-scoped runs, PASS6.265s/6.283s with0errors/warnings/sorries. All35 ordinary TCSlib
guards plus Nat.bits remain36 effective definitions, model default3 disabled, before complete
docs/headers/bodies. Exact wrapper removal recovers source0d. Fresh72 kernel-checked positive
identities and72 exact intended rfl-negative identities pass their checker; six synthetic
corruptions are rejected. Control runs are2.328s/2.433s, with the latter's72 expected failures,
not an owner proof failure. Entire100-file frozen folder/92UTF8 representations, full raw
types/AX and all attempts are supplied. This does not cure the ineffective instance controls.''')
replace('A separate fresh7.76s diagnostic checks the same prefix proof under arbitrary **local** Fintype',
'''A separate fresh current0d6.251s diagnostic checks the same prefix proof under arbitrary **local** Fintype''')
replace('a full two-instance seal, proof-value equivalence, or a public API change. Assess its exact limit.',
'''a full two-instance seal, proof-value equivalence, or a public API change. The earlier7.76s
f72 diagnostic remains separate historical evidence; the fresh current run preserves its
exact instrumentation and1385-byte output. Assess these exact generation-specific limits.''')
replace('''SCREEN23_FINAL_RESULTS_PENDING — final candidate will replace this marker only after the
independent reviewer freezes the actual complete23 BASE/HEAD evidence. No predicted metrics
or pass follow from the producer21 screen, current completed BASE alone or A's draft.''',
'''**Final current23 source comparison PASSED:** full issued21+Inclusions+ConfigCount, all46
Git/archive/inert/export captures exact at3023/0d. Eligible declarations1113→1124, directed
candidates647→648, reproduced normalized characters172081→172243; one new E3 row162/321,
zero gone and zero retained-score changes. All647BASE rows persist exactly; all648raw rows
are classified without a cap or a new debt acknowledgment. BASE702.217s is exactly adopted,
not rerun; current HEAD actually passed743.875s under shared lock/nice10/Python-I. All19
complete headers/chunks, nine delimiter controls, exact source/import/data/attribute freeze,
86→86 style findings and campaign0FAIL/23WARN→same are supplied; INFO's only normalized
change is private43→61. All32 same-kind/inline seam hits were inspected with no further exact
repoint found, a bounded comparison rather than a whole-library absence claim.

The final132-file final23-current folder and entire254-file resumed parent are frozen and
supplied. Original source-screen23's95files remain unchanged, with zero-byte/incomplete HEAD;
the resumed f72 HEAD was deliberately stopped obsolete at exit-15/357.643s/zero bytes after
the seam repair. Those attempts are not completed current comparisons. All raw partial,
failed and corrected parser/lint/classification evidence remains, not silently replaced.''')
draft+='''\n## Publication input fidelity\n\nThe final draft retains the exact624 issued path/order prefix and the full815 earlier draft\nscope. Every large metadata substitution is lossless and explicitly mapped; all existing\narchive aliases, all incoming/review/landing/issue material, every historical unissued draft\n(including publication-packet), complete current frozen evidence and full source populations\nremain represented. Original records are unchanged. Read final-publication-preparation's\nissued-to-current-partition, input inventory, folder coverage and alias receipts: all TCSlib/\nsections are read from source0d, every other path from the records candidate, matching the\nactual mixed-pin bundler. Fresh old captures cover every changed issued input. The original\n624 bundle independently reconstructs exactly8,707,327bytes/SHA8fa482702846898f7fa04c4e1b0aa012300b4febaa6385ee8caa869cf14740be.\n\nExact graph.py/transitive generator helpers, current gate119 closed-but-unmerged context and\ncomplete current-proof-readiness records are supplied. Readiness's GitHub mergeability is\nnull/unknown; this does not clear#235 or#215, whose external audits remain open. No source or\nrecords staging/publishing was performed by this input preparation. Root binds final adopted\nrecords/source pins and rendered bundle size/hash/count; no future self-commit hash is assumed.\n'''
assert 'CURRENT_SEALS_FINAL_RECEIPTS_PENDING' not in draft and 'SCREEN23_FINAL_RESULTS_PENDING' not in draft
(OUT/'canonical-pack-draft.md').write_text(draft)
canon='campaign/gates/120-f6-space-universal/pack.md';before=(R/canon).read_text() if (R/canon).exists() else ''
(OUT/'canonical-pack.patch').write_text(''.join(difflib.unified_diff(before.splitlines(keepends=True),draft.splitlines(keepends=True),fromfile='a/'+canon if before else '/dev/null',tofile='b/'+canon)))
save('pack-changes.json',dict(utc=NOW,root_draft=pin(ROOTBYTES),proposed_canonical=pin(draft.encode()),canonical_path=canon,
    exact_replacements=replacements,source=HEAD,root_draft_unchanged=True,canonical_not_written=True,
    status='Final evidence markers resolved only from frozen actual receipts; no gate/merge/readiness decision'))

save('frozen-evidence-checks.json',dict(utc=NOW,source=HEAD,frozen=frozen,root_draft_original=pin(ROOTBYTES),
    current_screen=pd,current_compiled_summary=summary,current_scoped_controls=controls,
    old_optional980MB_included_as_lossless_data_not_semantically_reviewed=True,no_new_Lean_or_screen=True))
save('current-context.json',dict(utc=NOW,observed_records=REC,not_final_records_pin=True,source=HEAD,base=BASE,
    gate119='CLOSED PASS0/0/0/17; #234 clear but unmerged and unused by F6',context_files=[dict(path=str(p.relative_to(R)),**filepin(p)) for p in context_files],
    readiness='Complete frozen10-file context; GitHub null/unknown is not merge clearance',
    final_binding_owner='Root; do not read SG1 mutable publication prep as current authority'))

own_fixed=['README.md','build-preparation.py','graph.py.txt','helper-provenance.json','issued-to-current-partition.json',
 'binary-alias-receipt.json','UTF8-substitution-receipt.json','canonical-pack-draft.md','canonical-pack.patch',
 'pack-changes.json','frozen-evidence-checks.json','current-context.json','folder-coverage.json','input-inventory.json',
 'source-bindings.json','BUNDLE-FILES-final-draft.txt','QA.json','MANIFEST.json']
(OUT/'build-preparation.py').write_bytes(Path(__file__).read_bytes())
readme='''# F6 final publication preparation

**Not yet clear to merge: #235 — the external audit remains open.**

This records-only draft resolves the root draft's pending current seals/screen markers from
the final frozen evidence. Canonical pack/list adoption, final records/source linkage,
rendered bundle checks, readiness and publication remain root-owned. Source0d550c59 is exact;
no source, canonical/root draft, frozen data or Git record was edited.

The original624 issued paths/order remain the literal leading prefix. Full815 old draft scope
is retained by unchanged literal sections or explicitly mapped lossless metadata encodings;
the old815 list/manifest and every historical draft remain included. All F6 incoming/review/
landing/issue material is uncapped. Every binary file has an exact full UTF8 alias, preserving
all10 existing aliases; every new metadata gzip/Base64 substitution has complete sizes/SHA256
and an independent deterministic roundtrip. Source captures, raw scores and control logs are
not substituted. The optional980,644,140-byte diagnostic is full lossless data, with streamed
UTF8/hash verification only; no theorem-value semantic review or native execution is claimed.

The inventory follows mkbundle-mixed EXACTLY: every TCSlib/ path from git source0d, all other
paths from the records candidate. Original624 mixed3023/f41 contents reconstruct exactly the
issued exchange bundle; fresh old captures cover all changed issued inputs. Pending canonical
pack.md uses canonical-pack-draft.md as an explicit prospective override. Source-bindings.json
lists every code blob. Root must rebind records changes after adoption/its final commit.

The complete final metadata100/92UTF8, full resumed screen254 and nested final132, original
screen95, preflight24, applied8 and MF62 20 files remain fully represented. Current193 raw
types/AX and fresh19scopes/72paired controls/arbitrary-witness diagnostic are supplied, with
their actual Fintype opacity limits. Actual replay lineage is MF61 full229 atf72 then WHOLE
MF61-clone MF62 two-module tail at0d; the21 inherited admissions remain. Original failed,
interrupted and obsolete screen/metadata attempts remain historical, not passing results.

The current small-glue table cites seamCompTM_step; current0d diagnostic6.251s is separate
from historicalf727.76s. The book-context limitation remains explicit. Gate119 is closed,
#234 clear but unmerged/unused; prospective-source readiness with null/unknown GitHub status
does not clear#235 or#215. No new reuse/debt/API/host decision is made by this preparation.

Inspect canonical-pack-draft.md and its concrete patch, full BUNDLE-FILES-final-draft.txt,
input-inventory/folder-coverage/source-bindings, both alias receipts and MANIFEST/QA. Decode
archives as data, never execute supplied code. Only the own standard-library builder ran.
No Lean, screen, snapshot/cache access, Git mutation, commit/push or external dispatch.
'''
(OUT/'README.md').write_text(readme)

def representation(rel):return binary_map.get(rel,encoded_map.get(rel,rel))
sections=[]
for rel in old815:
    p=representation(rel)
    if p not in sections:sections.append(p)
assert sections[:624]==issued
for rel in sorted(scope):
    p=representation(rel)
    if p not in sections:sections.append(p)
sections.append(canon)
for p in sorted(OUT.rglob('*')):
    if p.is_file():
        rel=str(Path(REL)/p.relative_to(OUT))
        if rel not in sections:sections.append(rel)
for name in own_fixed:
    rel=str(Path(REL)/name)
    if rel not in sections:sections.append(rel)
assert len(sections)==len(set(sections)) and all(representation(p) in sections for p in old815)
assert all(x['representation'] in sections for x in binary)
(OUT/'BUNDLE-FILES-final-draft.txt').write_text('\n'.join(sections)+'\n')
coverage=[]
for root in [F,G]:
    rows=[]
    for p in sorted(root.rglob('*')):
        rel=str(p.relative_to(R))
        if p.is_file() and not rel.startswith(REL+'/'):
            assert representation(rel) in sections,rel
            rows.append(dict(original=rel,represented_by=representation(rel)))
    coverage.append(dict(folder=str(root.relative_to(R)),files=len(rows),all_files_represented_without_cap=True,rows=rows))
save('folder-coverage.json',dict(utc=NOW,full815_scope=True,original624_prefix=True,folders=coverage))

inventory=[];bindings=[]
for rel in sections:
    if rel.startswith(REL+'/'):continue
    b=draft.encode() if rel==canon else mixed(rel);b.decode('utf-8')
    row=dict(path=rel,**pin(b),binding='prospective canonical draft, root adoption required' if rel==canon else 'source:'+HEAD if rel.startswith('TCSlib/') else 'records candidate, root final pin pending')
    inventory.append(row)
    if rel.startswith('TCSlib/'):
        bindings.append(dict(path=rel,source=HEAD,git_blob=git('rev-parse',HEAD+':'+rel).decode().strip(),**pin(b)))
save('input-inventory.json',dict(utc=NOW,source=HEAD,observed_records_not_final=REC,files=inventory,
    own_outputs='Own MANIFEST covers all new-folder payloads; no self-commit hash required',
    prospective_canonical_override=dict(path=canon,draft=str(Path(REL)/'canonical-pack-draft.md'),**pin(draft.encode()))))
save('source-bindings.json',dict(utc=NOW,source=HEAD,bundler_rule='p.startswith(TCSlib/) uses lean revision, all else records',
    all_TCSlib_paths_from_git_not_R_working_tree=True,all_source_rows=bindings,
    source_only_changed_from_comparison=['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean']))
qa=dict(utc=NOW,result='PASS complete final publication preparation; root adoption/render/publication pending',source=HEAD,
    original624_exact_prefix=True,original624_exact_mixed_bundle=pin(original),full815_scope_represented=True,
    all_existing10_aliases_preserved=True,new_binary_aliases=8,new_UTF8_original_substitutions=len(transforms),distinct_UTF8_encodings=len(dedup),
    total_sections=len(sections),mixed_source_bindings=len(bindings),all_sources_git_pinned=True,
    all_full_F6_material_represented=True,no_unresolved_current_evidence_markers=True,
    complete193_types_and_AXIOMS=True,current19scopes_72controls_and_witness_PASS=True,
    current_screen_counts=[1113,1124,647,648,172081,172243],MF61_MF62_generations_separate=True,
    full_unfiltered_optional_diagnostic_lossless=True,book_context_limit_preserved=True,
    payload_utf8_bytes=0,hosting_limit_bytes=100*1024*1024,no_canonical_or_frozen_mutation=True,
    no_Lean_screen_snapshot_cache_or_supplied_script_execution=True)
def payload():
    total=0
    for rel in sections:
        if rel.startswith(REL+'/'):b=(OUT/Path(rel).relative_to(REL)).read_bytes()
        elif rel==canon:b=draft.encode()
        else:b=mixed(rel)
        b.decode('utf-8');total+=len(b)
    return total
last=None
for _ in range(10):
    save('QA.json',qa)
    rows=[dict(path=str(p.relative_to(OUT)),**filepin(p)) for p in sorted(OUT.rglob('*')) if p.is_file() and p.name!='MANIFEST.json']
    save('MANIFEST.json',dict(utc=NOW,status='Frozen final publication preparation; root adoption and final pins remain pending',source=HEAD,files=rows))
    n=payload()
    if n==last:break
    qa['payload_utf8_bytes']=n;last=n
else:raise AssertionError('Payload length accounting did not stabilize')
assert payload()==qa['payload_utf8_bytes']<100*1024*1024
for row in load(OUT/'MANIFEST.json')['files']:assert filepin(OUT/row['path'])==dict(bytes=row['bytes'],sha256=row['sha256'])
assert all(str(Path(REL)/p.relative_to(OUT)) in sections for p in OUT.rglob('*') if p.is_file())
assert (ROOTD/'pack.candidate.md').read_bytes()==ROOTBYTES
for item in frozen:assert sha((R/item['folder']/'MANIFEST.json').read_bytes())==item['manifest_sha256']
print(json.dumps(dict(output=str(OUT),target=REL,sections=len(sections),payload_bytes=payload(),
    original624_prefix=True,scope815=True,new_UTF8_substitutions=len(transforms),encodings=len(dedup),
    binary_aliases=len(binary),source_bindings=len(bindings),own_files=sum(p.is_file() for p in OUT.rglob('*')),
    manifest_sha256=sha((OUT/'MANIFEST.json').read_bytes()),canonical_draft_sha256=sha(draft.encode())),indent=2))
