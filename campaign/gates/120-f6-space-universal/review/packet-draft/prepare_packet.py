from pathlib import Path,PurePosixPath
import base64,codecs,collections,datetime,gzip,hashlib,json,re,subprocess
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
F=R/'campaign/fills/f6';G=R/'campaign/gates/120-f6-space-universal'
S=Path('/private/tmp/tcslib-g120-packet-i4bplkqc');O=G/'review/packet-draft'
assert not O.exists(), 'new owned folder required'
O.mkdir(parents=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(R),*args])
def dump(name,value): (O/name).write_text(json.dumps(value,indent=2)+'\n')
source=git('rev-parse','f72a807e2376a2b986675c992745d6affc23b96f^{commit}').decode().strip()
base=git('rev-parse','3023dc1408c3d216fc07a7cbba9ae30135b861ed^{commit}').decode().strip()
issuedrecords=git('rev-parse','f41bdaea207724606d8934bfc2c9a823c5dd1e2f^{commit}').decode().strip()
observed=git('rev-parse','HEAD^{commit}').decode().strip()
for pin in [source,base,issuedrecords,observed]:git('cat-file','-e',pin+'^{commit}')
owner='TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'
before=git('show',base+':'+owner);after=git('show',source+':'+owner)
assert sha(before)=='1d7e0c7d706521991a623dfe6963650f867edfebe34c2dae8316e2078dc8069f'
assert sha(after)=='8a44b4b35010ac116e34880269b80d1121d2fdd86166e62da75efeffc984c031'
assert git('diff','--name-only',base,source,'--','*.lean').decode().splitlines()==[owner]
hdr=(F/'issue-preparation/inputs/space_universal-header.txt').read_bytes()
assert sha(hdr)=='89d2609a76de64f38283e2d9cf7338791aa451a7e08a46fb02f07eb182f5f62f'
assert hdr in before and hdr in after
assert after==(F/'landing/native1/Hierarchy.lean.txt').read_bytes()
assert after==(F/'landing/scoped-seals-v1/Owner-native.lean.txt').read_bytes()
(O/'space_universal-header.lean.txt').write_bytes(hdr)
for src,dest in [('pack.candidate.md','pack.candidate.md'),('QA-PLAN.md','QA-PLAN.md'),('BOOK-CONTEXT.md','BOOK-CONTEXT.md')]: (O/dest).write_bytes((S/src).read_bytes())
(O/'f6-full-file-inventory-at-task-start.txt').write_bytes((S/'f6-full-file-inventory.txt').read_bytes())
(O/'blueprint-file-inventory.txt').write_bytes((S/'blueprint-file-inventory.txt').read_bytes())
oldlist=(F/'BUNDLE-FILES.txt').read_text().splitlines();assert len(oldlist)==len(set(oldlist))==624
assert (F/'BUNDLE-FILES.txt').read_bytes()==git('show',issuedrecords+':campaign/fills/f6/BUNDLE-FILES.txt')
(O/'BUNDLE-FILES.issued-immutable.txt').write_text('\n'.join(oldlist)+'\n')
deferred_prefixes=['campaign/fills/f6/landing/replay-mf61/','campaign/fills/f6/landing/source-screen23/']
inventory=[str(p.relative_to(R)) for root in [F,G] for p in sorted(root.rglob('*')) if p.is_file() and O not in p.parents]
inventory=sorted(set(inventory))
(O/'complete-file-inventory-before.txt').write_text('\n'.join(inventory)+'\n')
histories=[];partition=[]
for rel in oldlist:
    pin=base if rel.startswith('TCSlib/') else issuedrecords
    original=git('show',pin+':'+rel)
    current=git('show',source+':'+rel) if rel.startswith('TCSlib/') else (R/rel).read_bytes()
    current.decode('utf-8')
    status='unchanged' if original==current else ('intentional source proof landing' if rel.startswith('TCSlib/') else 'updated records; final parent QA required')
    row={'path':rel,'issued_pin':pin,'issued_bytes':len(original),'issued_sha256':sha(original),'candidate_bytes':len(current),'candidate_sha256':sha(current),'status':status}
    if original!=current:
        p=O/'historical-issued'/Path(rel+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(original)
        row['full_issued_capture']=str(p.relative_to(R));histories.append(str(p.relative_to(R)))
    partition.append(row)
dump('issued-to-audit-input-partition.json',{'issued_bundle':{'source':base,'records':issuedrecords,'exchange':'2adb80788611696d2cad6f907285c0c5a197ae09','sections':624,'bytes':8707327,'sha256':'8fa482702846898f7fa04c4e1b0aa012300b4febaa6385ee8caa869cf14740be'},'issued_bundle_immutable_not_nested':True,'full_issued624_scope_retained':True,'candidate_source':source,'files':partition,'full_old_captures':histories})
population=(F/'issue-preparation/inputs/screen-population.txt').read_text().splitlines();assert len(population)==len(set(population))==21
extra=['TCSlib/Complexity/SpaceComplexity/Inclusions.lean','TCSlib/Complexity/SpaceComplexity/ConfigCount.lean']
population=population+extra;assert len(population)==len(set(population))==23
poprows=[]
for rel in population:
    a=git('show',base+':'+rel);b=git('show',source+':'+rel)
    if rel==owner:reason='Owned target, all new private assembly, actual proof/model/sketch and unchanged legacy context.'
    elif rel==extra[0]:reason='Full b2b_embed_refl identity-embedding comparison source newly cited by the producer/review.'
    elif rel==extra[1]:reason='Actual canonical visitedByTapeHead_mono citation used by the maintainer loop repoint.'
    elif rel.endswith('/Universal.lean'):reason='Issued conservative comparison/model-deviation coverage; do not fabricate it as a newly proved route prerequisite.'
    elif rel.endswith('/UniversalK.lean'):reason='Explicit frozen machinery and full ss_inputRewind_done stationary-action comparison source.'
    else:reason='Issued full route/model/public-host/field-reader source population; retained without narrowing or changing its original role.'
    poprows.append({'path':rel,'reason':reason,'base_bytes':len(a),'base_sha256':sha(a),'head_bytes':len(b),'head_sha256':sha(b),'changed':a!=b})
assert sum(x['changed'] for x in poprows)==1
(O/'source-population23.txt').write_text('\n'.join(population)+'\n')
dump('source-population23.json',{'source':source,'base':base,'files':poprows,'issued21_retained':True,'extra2':extra,'screens_status':'RUNNING by separate reviewer; no output read or count inferred here','no_new_screen_execution':True})
# Complete binary transport, never payload execution or filesystem ZIP extraction.
aliases=[];excluded=set()
for rel in inventory:
    if any(rel.startswith(x) for x in deferred_prefixes):continue
    p=R/rel
    if p.suffix not in ['.zip','.gz']:continue
    raw=p.read_bytes();excluded.add(rel)
    existing=Path(str(p)+'.base64.txt') if p.suffix=='.gz' else None
    if existing is not None and existing.is_file():
        encoded=existing.read_bytes();outpath=str(existing.relative_to(R))
    else:
        out=O/'utf8-archives'/Path(rel.replace('/','__')+'.base64.txt');out.parent.mkdir(exist_ok=True)
        encoded=base64.encodebytes(raw);out.write_bytes(encoded);outpath=str(out.relative_to(R))
    assert base64.b64decode(re.sub(rb'\s+',b'',encoded),validate=True)==raw
    encoded.decode('utf-8')
    row={'original':rel,'original_bytes':len(raw),'original_sha256':sha(raw),'UTF8_representation':outpath,'encoded_bytes':len(encoded),'encoded_sha256':sha(encoded),'exact_all_binary_bytes_round_trip':True}
    if p.suffix=='.gz':
        h=hashlib.sha256();n=0;decoder=codecs.getincrementaldecoder('utf-8')()
        with gzip.open(p,'rb') as stream:
            while True:
                chunk=stream.read(1024*1024)
                if not chunk:break
                h.update(chunk);n+=len(chunk);decoder.decode(chunk)
        decoder.decode(b'',final=True)
        row.update(complete_decoded_raw_bytes=n,complete_decoded_raw_sha256=h.hexdigest(),complete_decoded_UTF8=True)
        if p.name=='Fintype-uses-v2.out.gz':
            assert n==980644140 and h.hexdigest()=='e5ce734653e1ba528a10ea2b6622b048b26e79079427187cbfaa5b47b440b6e7'
            row['limit']='Optional overly-large complete theorem-value diagnostic retained as data, not semantically reviewed or needed for primary census.'
    aliases.append(row)
dump('utf8-archive-roundtrips.json',{'scope':'All three raw ZIPs and every completed-record gzip, exact complete binary transport, no scripts/extraction/Lean','archives':aliases})
# Independent data checks of the posted complete compiler maps, without any Lean.
C=F/'landing/compiled-accounting'
cb={x['name']:x for x in json.loads((C/'census-base.json').read_text())};ch={x['name']:x for x in json.loads((C/'census-head.json').read_text())}
ab={x['name']:x for x in json.loads((C/'allax-base.json').read_text())};ah={x['name']:x for x in json.loads((C/'allax-head.json').read_text())}
assert len(cb)==len(ab)==138 and len(ch)==len(ah)==193 and set(cb)==set(ab) and set(ch)==set(ah)
assert all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in ah.values())
assert not set(cb)-set(ch) and len(set(ch)-set(cb))==55
shared_changes=[n for n in cb if cb[n]!=ch[n]];assert not shared_changes
axchanges=[n for n in ab if ab[n]['axioms']!=ah[n]['axioms']];assert axchanges==['Complexity.space_universal']
delta=json.loads((C/'delta.json').read_text());classes=collections.Counter(x['classification'] for x in delta['added'])
assert dict(classes)=={'generated-target-proof-descendant':9,'authored-private-proof':18,'generated-private-proof-descendant':28}
assert len(json.loads((C/'targetax-head.json').read_text()))==56
counts=lambda rows:{'all':len(rows),'private':sum(x['private'] for x in rows.values()),'nonprivate':sum(not x['private'] for x in rows.values()),'nonprivate_noninternal':sum(not x['private'] and not x['internal'] for x in rows.values())}
dump('compiled-map-crosscheck.json',{'read_only_posted_maps_reconciled':True,'base':counts(cb),'head':counts(ch),'all193_standard':True,'all_shared_metadata_equal':True,'shared_AXIOM_changes':axchanges,'55_addition_classes':dict(classes),'target_f6_subset':56,'no_fresh_Lean_or_raw_output_reparse_by_this_preparation':True,'full_raw_native_maps_included_separately':True})
sp=json.loads((F/'landing/scoped-seals-v1/preparation.json').read_text());cv=json.loads((F/'landing/scoped-seals-v1/control-verification.json').read_text())
assert sp['head']==source and sp['source_sha256']==sha(after) and sp['section_count']==19 and len(sp['guards'])==36 and sp['TCSlib_effective_guards']==35
assert cv['result']=='PASS' and cv['exact_positive_identities']==cv['exact_expected_negative_identities']==72
assert len(cv['negative_corruption_cases'])==5
dump('native-seal-linkage.json',{'source':source,'source_sha256':sha(after),'native1_source_exact':True,'fresh_plain_owner_native_input_exact':True,'scoped_sections':19,'effective_regular_TCSlib':35,'extra_Mathlib':['Nat.bits'],'controls72_exact_checker_passed_as_supplied':True,'14_abbrevs_separate':True,'2_regular_Fintype_instances_ineffective':True,'finite_witness_diagnostic_is_conditional_altered_header_only':True,'no_child_Lean_run':True})
terms=['visitedByTapeHead','mem_visited','runFrom_add','Nat.find','exists_eq_add_of_le']
hits=[{'line':i,'text':line,'terms':[t for t in terms if t in line]} for i,line in enumerate(after.decode().splitlines(),1) if any(t in line for t in terms)]
dump('whole-owner-bounded-reuse-sweep.json',{'source_sha256':sha(after),'scope':'Complete owned source literal term sweep plus reading all18 new helpers/target, not a global equivalence proof','terms':terms,'all_hits':hits,'monotonicity_disposition':'The only named visited-set time-extension local is hmono715–717, now public canonical call. Other visited-set hits consume emitting/silent embedding public identities/frames; no second same-kind reconstruction identified.','not_a_debt_acknowledgment_or_all_library_absence_claim':True})
dump('pending-evidence.json',{'candidate_unissued':True,'final_records_pin':'PENDING PARENT','deferred_complete_subtrees':deferred_prefixes,'reason':'Both are currently live jobs. Do not read/hash mutable outputs. Parent appends each entire frozen folder, complete sources/archives/logs/order/launches/static/receipt/classifications, then rebuilds final list and index.','fresh_mf61_status':'RUNNING; no pass/count inferred','screen23_status':'RUNNING separate reviewer session7080, started2026-11-08T01:37:56UTC; no completed counts/pass inferred','book_context':'No authenticated chapter4 text; no fresh edition/full-book fidelity claim. Root may add verified primary context only if actually obtained.','finite_witness_diagnostic':'Completed conditional diagnostic to include in full; it does not expand actual-source two-instance opacity scope.'})
(O/'README.md').write_text('''# Gate120 F6 packet candidate

**Not yet clear to merge: #235 — external audit/final replay/screens/packet QA remain open.**

Record-only packet preparation for the explicitly selected Codex audit. The complete issued624
scope/order is inherited, with final proof, independent review, integration/native, all193 owner
compiler/AX data, fresh19-section/36-effective-definition seals/72 controls and the conditional
arbitrary-Fintype-witness diagnostic. All three rawZIPs and completed gzip outputs are supplied
as exact full UTF8 encodings, including the optional980MB diagnostic without semantic-review
claim. Full sources are23=issued21+Inclusions+ConfigCount; nine Mathlib homes were already fully
captured in the issued inputs. SourceF72 changes only Hierarchy; target header remains frozen.

pack.candidate.md, QA-PLAN.md and pending-evidence.json explicitly leave mf61 and new23-file
screen results pending/RUNNING. Their entire live subtrees are deferred, not sampled or hashed
mid-write. Parent appends complete frozen evidence and canonical pack/final records pin before
dispatch. Original624 packet remains immutable; its input partition/full old captures explain
intentional new source/current-record changes. No nested old bundle or old-digest substitution.

BOOK-CONTEXT.md records the absent authenticated chapter4 text and limits attribution claims.
No source/API/host/debt decision, Lean/screen/payload execution, Git mutation or publication.
Only this folder and private scratch written. Initial overly broad blueprint filename search
matched the repository path and its tool display was truncated; a full inventory was then saved
and filename-only checked. Complete inventories/input bytes drive this preparation, with no
listing caps. All final candidate-self/index/manifest verification remains parent QA.
''')
dump('context.json',{'source':source,'base':base,'issued_records':issuedrecords,'observed_records_HEAD_not_final_pin':observed,'final_records_pin':'PENDING PARENT','source_sha256':sha(after),'source_header_sha256':sha(hdr),'private_scratch':str(S),'source_scope':[owner],'no_Lean_screens_Git_mutation':True,'no_full_book_text_verified':True})
(O/'prepare_packet.py').write_bytes(Path(__file__).read_bytes())
planned=['BUNDLE-FILES.candidate.txt','candidate-input-review.json','MANIFEST.json']
finished=[p for p in inventory if not any(p.startswith(prefix) for prefix in deferred_prefixes)]
extras=set(finished)-set(oldlist)-excluded
extras.update(population)
extras.update(['campaign/backlog.md','machine-library-design.md'])
extras.update(str(p.relative_to(R)) for p in O.rglob('*') if p.is_file())
extras.update(str((O/p).relative_to(R)) for p in planned)
final=oldlist+sorted(extras-set(oldlist));assert len(final)==len(set(final)) and final[:624]==oldlist
for rel in final:
    p=PurePosixPath(rel);assert not p.is_absolute() and '..' not in p.parts and '\n' not in rel and '\r' not in rel
assert set(population)<=set(final)
assert all(a['UTF8_representation'] in final for a in aliases)
(O/'BUNDLE-FILES.candidate.txt').write_text('\n'.join(final)+'\n')
deferred_self={str((O/'candidate-input-review.json').relative_to(R)),str((O/'MANIFEST.json').relative_to(R))}
rows=[]
for rel in final:
    if rel in deferred_self:rows.append({'path':rel,'status':'Self/index or manifest deferred to parent final committed blob index'});continue
    if rel.startswith('TCSlib/'):data=git('show',source+':'+rel);location=source
    else:
        p=R/rel;assert p.is_file() and not p.is_symlink(),rel;data=p.read_bytes();location='records working tree candidate, final records pin pending'
    data.decode('utf-8');rows.append({'path':rel,'read_from':location,'bytes':len(data),'sha256':sha(data),'UTF8':True})
campaign_diff=git('diff','--name-only',base,observed,'--','*.lean').decode()
dump('candidate-input-review.json',{'source':source,'observed_records_HEAD_not_final_pin':observed,'final_records_pin':'PENDING PARENT','candidate_items':len(final),'issued_prefix':624,'appended':len(final)-624,'checked_UTF8_items':len(rows)-len(deferred_self),'known_payload_bytes_excluding_self':sum(x.get('bytes',0) for x in rows),'deferred_self':sorted(deferred_self),'deferred_live_subtrees':deferred_prefixes,'all_other_current_F6_gate_files_included_or_losslessly_aliased':True,'current_campaign_Lean_diff_from_base':campaign_diff,'no_fresh_native_or_screen_execution':True,'inputs':rows})
files=[]
for p in sorted(O.rglob('*')):
    if not p.is_file() or p==O/'MANIFEST.json':continue
    assert not p.is_symlink();b=p.read_bytes();files.append({'path':str(p.relative_to(O)),'bytes':len(b),'sha256':sha(b)})
manifest={'frozen_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source':source,'final_records_pin':'PENDING PARENT','status':'DRAFT candidate; live replay/screens deferred, no ready/gate verdict','candidate_items':len(final),'payload_files':len(files),'payload_bytes':sum(x['bytes'] for x in files),'files':files}
dump('MANIFEST.json',manifest)
print(json.dumps({'out':str(O),'manifest_sha256':sha((O/'MANIFEST.json').read_bytes()),'candidate_items':len(final),'inherited':624,'appended':len(final)-624,'payload_files':len(files),'payload_bytes':manifest['payload_bytes'],'binary_transports':len(aliases),'full_historical_captures':len(histories),'deferred_live_subtrees':deferred_prefixes,'observed_records':observed},indent=2))
