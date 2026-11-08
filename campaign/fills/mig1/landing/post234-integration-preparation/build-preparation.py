"""Read-only scoped source integration preparation for existing MIG landing #233.
Only own inert captures and patches are written. No supplied code or Lean runs.
"""
from pathlib import Path
import datetime,difflib,hashlib,json,re,shutil,subprocess

R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
P=R/'campaign/fills/mig1/landing/followup119-consumer-proposal'
PROBE=Path('/private/tmp/mig-post234-readonly-merge-probe')
OUT=Path('/private/tmp/mig-post234-integration-preparation-v1')
REL='campaign/fills/mig1/landing/post234-integration-preparation'
OUT.mkdir(exist_ok=False)
NOW=datetime.datetime.now(datetime.timezone.utc).isoformat()
sha=lambda b:hashlib.sha256(b).hexdigest()
load=lambda p:json.loads(p.read_text())
def pin(b):return dict(bytes=len(b),sha256=sha(b))
def save(name,data):
 p=OUT/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
def put(name,data):
 p=OUT/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
def git(*args):return subprocess.run(['git','-C',str(R),*args],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True).stdout
B1=git('rev-parse','origin/lean/mig1-mega-landing^{commit}').decode().strip()
CAM=git('rev-parse','bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c^{commit}').decode().strip()
assert B1=='b1f553b315f31b949076e91119473ce4070e7d53'
MB=git('merge-base',B1,CAM).decode().strip()
for rev in [B1,CAM,MB]:git('cat-file','-e',rev+'^{commit}')
manifest=load(P/'complete-manifest.json')
for row in manifest['files']:assert pin((P/row['path']).read_bytes())==dict(bytes=row['bytes'],sha256=row['sha256'])
F1=manifest['candidate_API_pin'];assert git('rev-parse',F1+'^{commit}').decode().strip()==F1;git('cat-file','-e',F1+'^{commit}')
assert not git('diff','--name-only',F1,CAM,'--','*.lean')
receipt=load(P/'generation2/receipt.json');freeze=load(P/'generation2/freeze.json')
assert receipt['baseline']==B1 and receipt['changes_count']==15 and len(freeze['changed_proof_bodies'])==14
probe=load(PROBE/'results.json');assert (probe['pr233'],probe['campaign'],probe['merge_base'])==(B1,CAM,MB)
files=[row['file'] for row in probe['results']]
expected=sorted(set(git('diff','--name-only',MB,B1,'--','*.lean').decode().splitlines())|set(git('diff','--name-only',MB,CAM,'--','*.lean').decode().splitlines()))
assert files==expected and len(files)==13
sources={};bindings=[]
for label,rev in [('pr233',B1),('merge-base',MB),('campaign',CAM)]:
 sources[label]={}
 for rel in files:
  data=(PROBE/label/(rel+'.txt')).read_bytes();assert data==git('show',rev+':'+rel)
  sources[label][rel]=data.decode();put('captures/'+label+'/'+rel+'.txt',data)
  bindings.append(dict(generation=label,commit=rev,path=rel,blob=git('rev-parse',rev+':'+rel).decode().strip(),**pin(data)))
raw={}
for row in probe['results']:
 rel=row['file'];b=(PROBE/'raw-prospective'/(rel+'.txt')).read_bytes();assert pin(b)==dict(bytes=row['bytes'],sha256=row['sha256'])
 raw[rel]=b.decode();put('captures/raw-three-way/'+rel+'.txt',b)
put('read-only-merge-probe-results.json',(PROBE/'results.json').read_bytes())

canonical=(R/'campaign/gates/119-mig1-followup-api/source/approved-moved-block.lean.txt').read_bytes()
assert len(canonical)==1043 and sha(canonical)=='3de684d6d30b02098aaf68c8b4223d9d8c92e2ff037505fdd3b5f494412baedf'
CAT='TCSlib/Complexity/TuringMachine/Build/Catalog.lean'
SIM='TCSlib/Complexity/TuringMachine/Simulation.lean'
WRAP='TCSlib/Complexity/TuringMachine/Build/Wrappers.lean'
assert sources['pr233'][CAT].count(canonical.decode())==1
assert sources['campaign'][WRAP].count(canonical.decode())==1 and canonical.decode() not in sources['campaign'][CAT]
conflict_re=re.compile(r'^<<<<<<< [^\n]*\n(.*?)^\|\|\|\|\|\|\| [^\n]*\n(.*?)^=======\n(.*?)^>>>>>>> [^\n]*\n',re.M|re.S)
merged={};conflicts=[]
for rel,text in raw.items():
 matches=list(conflict_re.finditer(text))
 if not matches:merged[rel]=text;continue
 assert len(matches)==1 and rel in [CAT,SIM]
 match=matches[0];ours,ancestor,theirs=match.groups()
 keep_ours=text[:match.start()]+ours+text[match.end():]
 assert keep_ours==sources['pr233'][rel]
 if rel==CAT:
  assert canonical.decode()==ours+'\n' and ancestor.endswith(theirs)
  assert 'private def f2_timedPadTM' in theirs and 'f2_timedPadTM' not in sources['pr233'][rel]
  merged[rel]=keep_ours.replace(canonical.decode(),'')
  action='Keep all MIG deletions; delete the B1 Catalog1043 redirect block. Keep gated1043 publisher in Wrappers. Do not take campaign side wholesale, which resurrects removed f2_timed machinery.'
 else:
  assert not ancestor and ours.startswith(theirs)
  assert 'theorem branchTM_k' in theirs and 'theorem branchTM_State' in theirs
  assert 'private lemma branchTM_initCfg_false' in ours and 'private lemma branchTM_initCfg_true' in ours
  merged[rel]=keep_ours
  action='Keep B1 block: the two public branch rows equal campaign exactly, plus the two MIG private initialization proofs. No new API decision.'
 conflicts.append(dict(file=rel,ours=pin(ours.encode()),ancestor=pin(ancestor.encode()),campaign=pin(theirs.encode()),resolution=action))
assert len(conflicts)==2
assert merged[WRAP].count(canonical.decode())==1 and 'theorem redirectTM_spaceUsedByTape' not in merged[CAT]
publisher_changes=sorted(rel for rel in files if merged[rel]!=sources['pr233'][rel])
assert publisher_changes==sorted([CAT,'TCSlib/Complexity/TuringMachine/Build/Primitives.lean',WRAP,'TCSlib/Complexity/TuringMachine/Encoding.lean','TCSlib/Complexity/TuringMachine/Finite.lean'])
for rel in files:put('captures/prospective-after-conflict-resolution/'+rel+'.txt',merged[rel].encode())

def header(text):
 depth=0;i=0
 while i<len(text):
  if text[i] in '([{⟨':depth+=1
  elif text[i] in ')]}⟩':depth-=1
  if not depth and text.startswith(':=',i):return text[:i+2]
  i+=1
 raise AssertionError('no declaration body delimiter')
body_after=merged.copy();edits=[]
for row in freeze['changed_proof_bodies']:
 rel=row['file'];name=row['name'].split('.')[-1];owner=Path(rel).stem
 before=(P/'generation2/inputs'/f'{owner}-{name}-before.lean.txt').read_text()
 after=(P/'generation2/inputs'/f'{owner}-{name}-after.lean.txt').read_text()
 assert sources['pr233'][rel].count(before)==1 and body_after[rel].count(before)==1,(rel,name)
 assert header(before)==header(after)
 body_after[rel]=body_after[rel].replace(before,after,1)
 api='Turing.pairDiagTM_spaceUsed' if name=='computesFunInTime_pairDup_spaceUsed' else 'Turing.FinTM.incFixedTM_spaceUsed' if name=='computesFunInTime_incFixed_spaceUsed' else 'Turing.MultiTapeTM.exists_first_entry_of_fixed' if 'exists_first_entry_of_fixed' in after else 'Turing.MultiTapeTM.exists_first_halt'
 assert api.split('.')[-1] in after
 edits.append(dict(file=rel,name=row['name'],private=row['private'],before=pin(before.encode()),after=pin(after.encode()),
     exact_surviving_header=pin(header(before).encode()),canonical_API=api,source_only=True))
assert len(edits)==14 and len({x['file'] for x in edits})==6
for rel in files:put('captures/after14-consumer-bodies/'+rel+'.txt',body_after[rel].encode())

# Apply the already approved optional comments as exact scoped text hunks, not scripts/full files.
def apply_scoped_diff(contents,patch):
 lines=patch.splitlines(keepends=True);i=0;out=contents.copy();hunks=[]
 while i<len(lines):
  if not lines[i].startswith('--- a/'):i+=1;continue
  oldrel=lines[i][6:].strip();i+=1;assert lines[i].startswith('+++ b/');rel=lines[i][6:].strip();assert rel==oldrel;i+=1
  while i<len(lines) and not lines[i].startswith('--- a/'):
   if not lines[i].startswith('@@ '):i+=1;continue
   mark=lines[i].rstrip();i+=1;old=[];new=[]
   while i<len(lines) and not lines[i].startswith(('@@ ','--- a/')):
    line=lines[i];i+=1
    if line.startswith(' '):old.append(line[1:]);new.append(line[1:])
    elif line.startswith('-'):old.append(line[1:])
    elif line.startswith('+'):new.append(line[1:])
    elif line.startswith('\\ No newline'):raise AssertionError('unexpected no-newline marker')
    else:raise AssertionError(repr(line))
   a=''.join(old);b=''.join(new);assert out[rel].count(a)==1,(rel,mark)
   out[rel]=out[rel].replace(a,b,1);hunks.append(dict(file=rel,original_hunk=mark,old=pin(a.encode()),new=pin(b.encode())))
 return out,hunks
final,doc_hunks=apply_scoped_diff(body_after,(P/'generation2/optional-sketches-after-bodies.patch').read_text())
assert len(doc_hunks)==15
def code_without_comments(text):
 i=0;out=[];depth=0
 while i<len(text):
  if depth:
   if text.startswith('/-',i):depth+=1;i+=2
   elif text.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif text.startswith('/-',i):depth=1;i+=2
  elif text.startswith('--',i):
   j=text.find('\n',i);i=len(text) if j<0 else j
  else:out.append(text[i]);i+=1
 assert not depth
 return re.sub(r'\s+','',''.join(out))
for rel in files:
 assert code_without_comments(body_after[rel])==code_without_comments(final[rel])
 assert re.findall(r'^import .+$',merged[rel],re.M)==re.findall(r'^import .+$',final[rel],re.M)
 assert not re.search(r'(?m)^(?:<<<<<<<|\|\|\|\|\|\|\||=======|>>>>>>>)',final[rel])
 put('captures/final-proposed-with-approved-sketches/'+rel+'.txt',final[rel].encode())
assert final[WRAP].count(canonical.decode())==1 and 'theorem redirectTM_spaceUsedByTape' not in final[CAT]
assert final['TCSlib/Complexity/RAMSimulation/WordSize.lean']==sources['pr233']['TCSlib/Complexity/RAMSimulation/WordSize.lean']

def diff(a,b):
 return ''.join(''.join(difflib.unified_diff(a[rel].splitlines(keepends=True),b[rel].splitlines(keepends=True),fromfile='a/'+rel,tofile='b/'+rel)) for rel in files if a[rel]!=b[rel])
patches=[('000-reference-campaign-api-merge.patch',sources['pr233'],merged),
 ('001-post-merge-consumer-bodies.patch',merged,body_after),('002-approved-sketch-synchronization.patch',body_after,final),
 ('all-integration-from-B1-reference.patch',sources['pr233'],final)]
roundtrips=[]
for name,a,b in patches:
 text=diff(a,b);put(name,text.encode());applied,_=apply_scoped_diff(a,text);assert applied==b
 reverse=diff(b,a);recovered,_=apply_scoped_diff(b,reverse);assert recovered==a
 roundtrips.append(dict(patch=name,changed_files=[rel for rel in files if a[rel]!=b[rel]],forward_exact=True,reverse_exact=True,sha256=sha(text.encode())))

def declaration(text,name):
 m=re.search(r'(?m)^(?:theorem|lemma) '+re.escape(name)+r'\b',text);assert m,name
 start=text.rfind('/--',0,m.start());assert start>=0
 tail=text[m.end():];end=re.search(r'(?m)^(?:/--|(?:private )?(?:theorem|lemma|def|instance|structure|inductive)\b|end\b|namespace\b)',tail)
 stop=m.end()+end.start() if end else len(text)
 return text[start:stop]
api_specs=[('Turing.MultiTapeTM.exists_first_halt','TCSlib/Complexity/TuringMachine/Finite.lean'),
 ('Turing.MultiTapeTM.exists_first_entry_of_fixed','TCSlib/Complexity/TuringMachine/Finite.lean'),
 ('Turing.pairDiagTM_spaceUsed','TCSlib/Complexity/TuringMachine/Encoding.lean'),
 ('Turing.FinTM.incFixedTM_spaceUsed','TCSlib/Complexity/TuringMachine/Build/Primitives.lean')]
api_rows=[]
for name,rel in api_specs:
 chunk=declaration(sources['campaign'][rel],name.split('.')[-1]);assert chunk in final[rel]
 put('api-bindings/'+name+'.lean.txt',chunk.encode())
 api_rows.append(dict(name=name,home=rel,publisher_commit=CAM,source_blob=git('rev-parse',CAM+':'+rel).decode().strip(),
    full_capture=str(Path(REL)/'api-bindings'/(name+'.lean.txt')),**pin(chunk.encode()),exact_in_proposed_owner=True))
put('api-bindings/Turing.FinTM.redirectTM_spaceUsedByTape.lean.txt',canonical)
api_rows.append(dict(name='Turing.FinTM.redirectTM_spaceUsedByTape',home=WRAP,publisher_commit=CAM,
 full_capture=str(Path(REL)/'api-bindings/Turing.FinTM.redirectTM_spaceUsedByTape.lean.txt'),**pin(canonical),
 exact_in_merged_Wrappers=True,Catalog_duplicate_absent=True,not_ancestor1013byte_body=True))
save('API-BINDINGS.json',dict(utc=NOW,merged_publisher=CAM,publisher_Lean_exact_API119_head=F1,APIs=api_rows,
    consumer_mappings=edits,live_stop_sites=sum('exists_first_entry_of_fixed' in x['canonical_API'] for x in edits),
    existing_NONE_first_halt_sites=sum('exists_first_halt' in x['canonical_API'] for x in edits),zero_space_sites=2,
    moved_Catalog_duplicate_counted_as_15th_change=True))
save('SOURCE-PINS.json',dict(utc=NOW,observed_pushed_PR233=B1,merged_campaign=CAM,actual_Git_merge_base=MB,
    proof_comparison_base='3023dc1408c3d216fc07a7cbba9ae30135b861ed',comparison_base_is_not_Git_merge_base=True,
    proposal_manifest=dict(path=str((P/'complete-manifest.json').relative_to(R)),sha256=sha((P/'complete-manifest.json').read_bytes()),payloads_verified=len(manifest['files'])),
    source_captures=bindings,source_files_union=files,source_or_Git_mutation=False))
save('CONFLICT-RESOLUTION.json',dict(utc=NOW,conflicts=conflicts,mechanical_no_new_decision=True,
    publisher_delta_files=publisher_changes,canonical_redirect1043=pin(canonical),
    exact_global_name_home_preserved='Turing.FinTM.redirectTM_spaceUsedByTape in Build/Wrappers',
    read_only_reconstruction='git merge-file -p --diff3 on own inert captures in private scratch, no repository/index/object writes',
    warning='Reference000 patch describes merge result; do not apply it again after campaign merge. Do not select whole Catalog campaign conflict side.'))
save('PATCH-ROUNDTRIPS.json',dict(utc=NOW,patches=roundtrips,actual_postmerge_14_scoped_bodies=edits,
    approved_comment_hunks=doc_hunks,all14_headers_exact=True,all_non_target_code_preserved=True,
    no_import_runtime_machine_or_instance_edits=True,three_RAM_source_residuals_byte_unchanged=True,
    canonical_Wrappers1043_exact=True,Catalog_duplicate_removed=True,
    no_Lean_native_AX_seal_replay_screen_run=True,
    validation_limit='Only source construction/roundtrips. Existing generation1 small3forwarders+2spaceleaves native evidence remains separately scoped; all integrated modules and9later rewrites require actual root validation.'))
put('build-preparation.py',Path(__file__).read_bytes())
readme=f'''# Post-#234 scoped MIG integration preparation

**Not yet clear to merge: #233 — integration, actual validation and gate118 remain pending.**

#234 was merged by Seyoon at `{CAM}`, with exactly the gatedF1 Lean tree. The current pushed
MIG source was `{B1}`. This folder is a read-only plan/scoped patch for those exact parents,
not a new fill or an applied source integration. The actual Git merge base is `{MB}`;
3023 remains the earlier proof-comparison base and is not misrepresented as the merge base.

Two textual merge conflicts require mechanical preservation:

- **Catalog declaration modify/delete:** B1 retains the1043-byte improved redirect-space
  theorem while the campaign removes its old home. The broad conflict also contains old
  `f2_timed*` machinery that MIG already deleted. Preserve all MIG deletions; remove only
  the B1 duplicate theorem. Keep the exact gated1043-byte body in Wrappers, not the older
 1013-byte Catalog implementation. Its SHA256 is
  `3de684d6d30b02098aaf68c8b4223d9d8c92e2ff037505fdd3b5f494412baedf`.
- **Simulation concurrent insertion:** keep the B1 block. Its public branchTM_k/State rows
  equal the campaign rows byte-for-byte, and its private branchTM_initCfg_false/true proofs
  must remain. No new statement/API choice is required.

After root merges campaign and resolves those conflicts, validate the complete prospective
source hashes in captures/prospective-after-conflict-resolution. Then apply
`001-post-merge-consumer-bodies.patch`, the14 exact approved consumer replacements in6files.
The original15th change (Catalog duplicate deletion) is already discharged by conflict
resolution. Apply `002-approved-sketch-synchronization.patch` next: the previously approved
14 sketch updates and Catalog owner-index comment only. Neither patch uses old whole-file
after copies. They were constructed on the actual three-way source union and preserve every
publisher addition. `000-reference-campaign-api-merge.patch` and the combined B1 reference
patch are review aids, not instructions to reapply the campaign changes after merging.

The five LIVE-stop uses consume the merged arbitrary-predicate full-configuration fixed-entry
contract. Seven NONE-first-halt uses consume the pre-existing public theorem; none is silently
converted into a LIVE-stop instance. The two constant-space leaves cite the newly merged
pairDiag/incFixed zero-space equations. Names/headers/imports/machines/instances and other
MIG proof bytes are preserved; all17 previously filled targets stay untouched by these scoped
edits, and the complete WordSize source holding the3RAM residuals is byte-identical to B1.
The global redirect theorem remains once, in Wrappers. Exact API publisher/source bindings,
inert before/after captures and forward/reverse patch checks are recorded in this folder.

Root owns the actual campaign merge, scoped application, commit/push and strong validation:
actual owner/dependency chain on complete mac5 context; current owned AX/census; direct
argument review plus changed-region seals/paired controls; source/runtime/header freeze;
and a fresh merged-tree downstream replay, then the selected Codex gate118. The earlier
generation1 small native checks do not validate these integrated whole modules. Nine later
production rewrites remain source-only evidence until that execution; retained legacy reader
sites can still require routine mechanical fixes during root's strong seals. No new API/import,
debt/route/statement decision is identified by this preparation, and no new proof fill occurred.

No source/canonical/Git mutation, Lean, screen, snapshot/cache write, commit/push or dispatch
was performed. Only own inert scratch/output files were written. Supplied scripts were read
as data and not executed. A read-only inspection initially mistyped the env path and was
immediately rerun with the exact required environment before using its results; all final
preparation commands used the required env and Python-I. The own builder is retained as data.
'''
put('README.md',readme.encode())
rows=[dict(path=str(p.relative_to(OUT)),**pin(p.read_bytes())) for p in sorted(OUT.rglob('*')) if p.is_file()]
save('MANIFEST.json',dict(utc=NOW,status='Frozen read-only scoped integration preparation; no applied/native/gate claim',
    PR233_source=B1,campaign_source=CAM,files=rows))
for row in load(OUT/'MANIFEST.json')['files']:assert pin((OUT/row['path']).read_bytes())==dict(bytes=row['bytes'],sha256=row['sha256'])
print(json.dumps(dict(output=str(OUT),target=REL,files=len(rows)+1,source_union_files=len(files),merge_conflicts=2,
    scoped_postmerge_proofs=14,original_authorized_changes=15,consumer_files=6,
    canonical1043_preserved=True,no_unavoidable_new_decision=True,
    manifest_sha256=sha((OUT/'MANIFEST.json').read_bytes())),indent=2))
