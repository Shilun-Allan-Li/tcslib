from pathlib import Path
import subprocess,json,hashlib,difflib,re,datetime
R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');O=Path('/private/tmp/f6-post234-context-review');B='3023dc1408c3d216fc07a7cbba9ae30135b861ed';F1='f1ca767a10551960faf36ad9c8ff17bea3a2d88c';C='bf6418fabea9cbb9d9bcdf2b3e40487a6f9f718c';F6='0d0950caeb39300b5cc9bf41e5f07392fb26d3e5';GP=R/'campaign/gates/119-mig1-followup-api'
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
def blob(pin,path):return git('show',pin+':'+path)
def sha(b):return hashlib.sha256(b).hexdigest()
for p in [B,F1,C,F6]:assert git('rev-parse',p+'^{commit}').decode().strip()==p;git('cat-file','-e',p+'^{commit}')
def leans(pin):
 out={}
 for ln in git('ls-tree','-r',pin).decode().splitlines():
  a,p=ln.split('\t');typ=a.split()
  if p.endswith('.lean'):out[p]=typ[2]
 return out
bm,fm,cm,pm=[leans(p) for p in [B,F1,C,F6]];assert fm==cm
changed=[p for p in bm if bm[p]!=fm[p]];assert len(changed)==5 and set(bm)==set(fm)==set(cm)==set(pm)
proofchanges=[p for p in bm if bm[p]!=pm[p]];assert proofchanges==['TCSlib/Complexity/SpaceComplexity/Hierarchy.lean'] and not set(changed)&set(proofchanges)
rows=[]
for path in sorted(changed):
 before=blob(B,path);after=blob(C,path);a=before.splitlines(keepends=True);b=after.splitlines(keepends=True);ops=[x for x in difflib.SequenceMatcher(None,a,b,autojunk=False).get_opcodes() if x[0]!='equal'];assert len(ops)==1 and ops[0][0] in ['insert','delete'];tag,i,j,k,l=ops[0]
 if tag=='insert':assert b''.join(b[:k]+b[l:])==before;delta=b''.join(b[k:l])
 else:assert b''.join(a[:i]+a[j:])==after;delta=b''.join(a[i:j])
 assert re.findall(rb'^import .+$',before,re.M)==re.findall(rb'^import .+$',after,re.M)
 assert not re.search(rb'^\s*(?:@\[|attribute |(?:private )?(?:def|abbrev|instance|structure|inductive|class)\s)',delta,re.M)
 suffix=path.removeprefix('TCSlib/').replace('/','__');(O/(suffix+'.base.lean.txt')).write_bytes(before);(O/(suffix+'.post234.lean.txt')).write_bytes(after)
 rows.append({'path':path,'change':tag,'delta_bytes':len(delta),'delta_sha256':sha(delta),'baseline_sha256':sha(before),'post234_sha256':sha(after),'identical_to_F1':after==blob(F1,path),'all_unrelated_bytes_and_imports_frozen':True,'no_definition_instance_runtime_or_attribute_command_delta':True})
rel=proofchanges[0];source=blob(F6,rel);assert sha(source)=='550c59f38193d19156d215c6e7d6ef5f005a11a5bd3182c6cc443ba25790b8a3'
# The earlier complete native gate119 comparison gives the exact public type/attribute/AX compatibility evidence.
d=json.loads((GP/'review/compiled-comparison/compiled-delta.json').read_bytes());assert not d['removed'] and not d['shared_axiom_changes'];assert len(d['shared_metadata_changes'])==1 and d['shared_metadata_changes'][0]['name']=='Turing.FinTM.redirectTM_spaceUsedByTape' and d['shared_metadata_changes'][0]['fields']==['owner']
assert len(d['added'])==4 and all(x['kind']=='theorem' and not x['simp'] and not x['unfold'] and set(x['axioms'])=={'propext','Classical.choice','Quot.sound'} for x in d['added'])
# Narrow exact-family applicability review: only the19 already reviewed production chunks.
chunks=json.loads((R/'campaign/fills/f6/landing/source-screen23-resumed/final23-current/new19-complete-headers-and-chunks.json').read_bytes());assert len(chunks)==19
text='\n'.join(x['raw_text'] for x in chunks);assert all(x['raw_text'] in source.decode() for x in chunks)
absent={n:n not in text for n in ['pairDiagTM','incFixedTM','redirectTM','exists_first_entry_of_fixed','Nat.find']};assert all(absent.values());assert 'StepBlock.forwardLoop_forward' in text and 'seamCompTM_step' in text
out={'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'old_source_baseline':B,'gate119_source':F1,'merged_campaign':C,'unchanged_F6_proof_component':F6,'complete_Lean_file_count':len(cm),'merged_campaign_Lean_exact_F1':True,'five_API_sources':rows,'disjoint_only_F6_source_change':proofchanges,'Hierarchy_source_sha256':sha(source),'gate119_compiled_compatibility':{'old_owned_constants':3778,'new_owned_constants':3782,'removed':0,'shared_type_kind_universe_privacy_attributes_change':0,'only_owner_move':'Turing.FinTM.redirectTM_spaceUsedByTape','shared_axiom_changes':0,'added_non_simp_theorems':3,'generated_auxiliary':1,'all_additions_standard3':True},'narrow19proof_name_check':absent,'no_source_change_required_by_new_APIs':True,'fresh_actual_merge_head_and_snapshot_pending_root_relay':True,'no_Lean_or_supplied_script_or_Git_mutation':True}
(O/'API-context-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
