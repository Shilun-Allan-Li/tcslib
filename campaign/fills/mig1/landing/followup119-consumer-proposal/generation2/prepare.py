"""Source-only exact fifteen-change proposal. Never touches actual checkout or Git."""
from pathlib import Path
import datetime,difflib,hashlib,json,re
p=Path(__file__).resolve().parent;parent=p.parent
H=lambda b:hashlib.sha256(b).hexdigest()
base='b1f553b315f31b949076e91119473ce4070e7d53'
sweep=json.loads((parent/'sweep-inventory.json').read_text())
sources={row['file'].split('/')[-1][:-5]:(parent/'sweep-inputs'/(row['file'].replace('/','__')+'.txt')).read_text() for row in sweep['source_files']}
proposed=dict(sources);changes=[]
def chunk(src,name,private=True):
 pat=('private lemma ' if private else '(?:lemma|theorem) ')+re.escape(name)+r'\b'
 m=re.search(r'(?m)^'+pat,src);assert m,name
 a=m.start();z=src.find('\n/--',a);z=len(src) if z<0 else z+1
 return a,z,src[a:z]
def apply(owner,name,transform,kind,private=True):
 s=proposed[owner];a,z,old=chunk(s,name,private);new=transform(old)
 assert old!=new
 # Every selected header has no statement-level ':=' let: exact literal ':= by' is checked.
 sep=':= by' if ':= by' in old else ':='
 assert old.split(sep,1)[0]==new.split(sep,1)[0],name
 assert 'Nat.find' not in new,name
 proposed[owner]=s[:a]+new+s[z:]
 for label,txt in [('before',old),('after',new)]:
  (p/'inputs'/f'{owner}-{name}-{label}.lean.txt').write_text(txt)
 changes.append({'file':owner,'declaration':name,'private':private,'kind':kind,'header_exact':True,'before_sha256':H(old.encode()),'after_sha256':H(new.encode()),'validation':'Source-only; initial3 forwarding bodies and2leaf expressions match separately native-tested generation1, not a whole production module check' if kind=='generation1_reuse' else 'Source-only exact local rewrite; no native/full-module/seal pass claimed'})
def saved(owner,name):return (parent/'inputs'/f'{owner}-{name}-after.lean.txt').read_text()
for owner,name in [('Loop','emCall_first_entry'),('Primitives','catalogFirstEntry'),('Primitives','emitter_first_entry')]:
 apply(owner,name,lambda old,o=owner,n=name:saved(o,n),'generation1_reuse')
for name in ['computesFunInTime_pairDup_spaceUsed','computesFunInTime_incFixed_spaceUsed']:
 apply('Catalog',name,lambda old,n=name:saved('Catalog',n),'generation1_reuse',private=False)
# Seventh, already reviewed as a source-only local extraction.
apply('Loop','emCall_eval_first',lambda old:saved('Loop','emCall_eval_first'),'existing_NONE_first_halt')
# Six further NONE-first-halt local extraction blocks, preserving all rest of each body.
def right(old):
 a=old.index('  have hex :');z=old.index('  have hi :',a)
 new='''  obtain ⟨t, ht, hlive, heq⟩ :=
    MultiTapeTM.exists_first_halt M.tm (M.tm.initCfg x) hc
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have hs : c.state = none := by
    change (M.tm.runFrom (M.tm.initCfg x) t).state = none
    rw [heq]
    exact hc
  have hcT : M.tm.runFrom (M.tm.initCfg x) T = c := heq.symm
'''
 result=old[:a]+new+old[z:]
 needle='(fun j hj => Nat.find_min hex hj)';assert result.count(needle)==1
 return result.replace(needle,'hlive')
apply('Loop','emCall_right_endpoint',right,'existing_NONE_first_halt')
def length(old):
 a=old.index('  have hh : ∃ t,');z=old.index('  let emb :',a)
 new='''  have hspec := (computesInTime_iff M x w T).mp hM
  obtain ⟨t, ht, hlive, heq⟩ :=
    MultiTapeTM.exists_first_halt M.tm (M.tm.initCfg x) hspec.1
  let c := M.tm.runFrom (M.tm.initCfg x) t
  have hs : c.state = none := by
    change (M.tm.runFrom (M.tm.initCfg x) t).state = none
    rw [heq]
    exact hspec.1
  have ho : c.output = w := by
    change (M.tm.runFrom (M.tm.initCfg x) t).output = w
    rw [heq]
    exact hspec.2
'''
 result=old[:a]+new+old[z:];needle='(fun s hst => Nat.find_min hh hst)';assert result.count(needle)==1
 return result.replace(needle,'hlive')
apply('Primitives','lenStart',length,'existing_NONE_first_halt')
def count(old):
 a=old.index('  have hh : ∃ t,');z=old.index('  have hp (j :',a)
 new='''  have hhalt : (M.tm.runFrom c T).state = none := by rw [hT]; rfl
  obtain ⟨t, ht, hlive, heq⟩ := MultiTapeTM.exists_first_halt M.tm c hhalt
  have he : M.tm.runFrom c t = d := heq.trans hT
'''
 result=old[:a]+new+old[z:];needle='(fun l hl => Nat.find_min hh (by omega))';assert result.count(needle)==1
 return result.replace(needle,'(fun l hl => hlive l (by omega))')
apply('Primitives','splitBody_count',count,'existing_NONE_first_halt')
def timed(old):
 a=old.index('  have hh : ∃ t,');z=old.index('  have hcap :',a)
 new='''  have hspec := (computesInTime_iff D x [b] T).mp hD
  obtain ⟨t, ht, hlive, heq⟩ :=
    MultiTapeTM.exists_first_halt D.tm (D.tm.initCfg x) hspec.1
  let c := D.tm.runFrom (D.tm.initCfg x) t
  have hs : c.state = none := by
    change (D.tm.runFrom (D.tm.initCfg x) t).state = none
    rw [heq]
    exact hspec.1
  have ho : c.output = [b] := by
    change (D.tm.runFrom (D.tm.initCfg x) t).output = [b]
    rw [heq]
    exact hspec.2
'''
 result=old[:a]+new+old[z:];needle='(fun s hst => Nat.find_min hh hst)';assert result.count(needle)==1
 return result.replace(needle,'hlive')
apply('Wrappers','timed_start',timed,'existing_NONE_first_halt')
def cond(old):
 a=old.index('  have hh : ∃ t,');z=old.index('  have hi :',a)
 new='''  have hspec := (computesInTime_iff D x [b] tD).mp hDc
  obtain ⟨t, _ht, hlive, heq⟩ :=
    MultiTapeTM.exists_first_halt D.tm (D.tm.initCfg x) hspec.1
  let cf := D.tm.runFrom (D.tm.initCfg x) t
  have hstop : cf.state = none := by
    change (D.tm.runFrom (D.tm.initCfg x) t).state = none
    rw [heq]
    exact hspec.1
  have hout : cf.output = [b] := by
    change (D.tm.runFrom (D.tm.initCfg x) t).output = [b]
    rw [heq]
    exact hspec.2
'''
 result=old[:a]+new+old[z:];needle='(fun s hs => Nat.find_min hh hs)';assert result.count(needle)==1
 return result.replace(needle,'hlive')
apply('Composition','condTM_start',cond,'existing_NONE_first_halt')
def buffered(old):
 a=old.index('  have hh : ∃ t,');z=old.index('  refine ⟨t +',a)
 new='''  have hspec := (computesInTime_iff M₁ x y t₁).mp h₁
  obtain ⟨t, ht, hlive, heq⟩ :=
    MultiTapeTM.exists_first_halt M₁.tm (M₁.tm.initCfg x) hspec.1
  let c := M₁.tm.runFrom (M₁.tm.initCfg x) t
  have hs : c.state = none := by
    change (M₁.tm.runFrom (M₁.tm.initCfg x) t).state = none
    rw [heq]
    exact hspec.1
  have ho : c.output = y := by
    change (M₁.tm.runFrom (M₁.tm.initCfg x) t).output = y
    rw [heq]
    exact hspec.2
'''
 result=old[:a]+new+old[z:];needle='(fun s hs => Nat.find_min hh hs)';assert result.count(needle)==1
 return result.replace(needle,'hlive')
apply('Simulation','bufferedComp_start',buffered,'existing_NONE_first_halt',private=False)
# Existing exact live-stop hypothesis/cut: only source entry selection is forwarded.
def embed(old):
 a=old.index('  have hex :');z=old.index('  have hp :',a)
 new='''  obtain ⟨t, ht, hcut, he⟩ :=
    MultiTapeTM.exists_first_entry_of_fixed tm stop c d T hfix hd hT
'''
 result=old[:a]+new+old[z:];needle='Nat.find_min hex (by omega) ⟨q, hz, hq⟩';assert result.count(needle)==1
 return result.replace(needle,'hcut j (by omega) ⟨q, hz, hq⟩')
apply('Primitives','splitEmbed_cut',embed,'API119_inline_live_stop')
# Setup's existing all-configuration stationarity supplies the fixed-step premise.
def launch(old):
 a=old.index('  have hex :');z=old.index('  have hprefix ',a)
 new='''  let stop : FwdMapState M.State → Prop := fun r => ∃ q tag, r = .run q tag
  have hfix : ∀ z : Cfg (1 + (1 + M.k)) Bool (FwdMapState M.State) x,
      (∃ r, z.state = some r ∧ stop r) → (fwdMapTM M false).tm.step z = z := by
    rintro z ⟨r, hr, q, tag, hq⟩
    have hentered : fwdMapEntered M z := ⟨q, tag, by rw [hr, hq]⟩
    have hs := fwdMapSetup_stationary M z hentered 1
    simpa only [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero] using hs
  have hdstop : ∃ r,
      (fwdMapVirtual M (M.tm.initCfg b) true ⟨x.length + 1, by omega⟩ a
        (pairEncode a [])).state = some r ∧ stop r := by
    refine ⟨.run M.tm.q₀ true, ?_, M.tm.q₀, true, rfl⟩
    simp only [fwdMapVirtual, MultiTapeTM.initCfg_eq, Cfg.init_state, Option.map_some]
  obtain ⟨u, hu, hcut, hefirst⟩ := MultiTapeTM.exists_first_entry_of_fixed
    (fwdMapTM M false).tm stop ((fwdMapTM M false).tm.initCfg x)
    (fwdMapVirtual M (M.tm.initCfg b) true ⟨x.length + 1, by omega⟩ a
      (pairEncode a [])) t hfix hdstop he
  have hg : ∀ v < u, ¬fwdMapEntered M
      ((fwdMapTM M false).tm.runFrom ((fwdMapTM M false).tm.initCfg x) v) := by
    rintro v hv ⟨q, tag, hq⟩
    exact hcut v hv ⟨.run q tag, hq, q, tag, rfl⟩
'''
 result=old[:a]+new+old[z:]
 a=result.index('  have hs := fwdMapSetup_stationary',result.index('  have hprefix '))
 return result[:a]+'  exact hefirst\n\n'
apply('Primitives','fwdMap_launch',launch,'API119_inline_live_stop')
# Exact duplicate moved owner is supplied by merged API119; no global API deletion.
s=proposed['Catalog'];a,z,old=chunk(s,'redirectTM_spaceUsedByTape',False);start=s.rfind('/--',0,a)
block=s[start:z];assert block==(parent/'inputs/removed-Catalog-redirect-block.lean.txt').read_text()
proposed['Catalog']=s[:start]+s[z:]
changes.append({'file':'Catalog','declaration':'redirectTM_spaceUsedByTape','kind':'API119_exact_owner_adoption','global_name_retained_in':'TCSlib.Complexity.TuringMachine.Build.Wrappers','removed_block_sha256':H(block.encode()),'bytes':len(block.encode()),'validation':'Exact approved existing1043byte block, byte-compared to actualAPI119publisher in generation1; no global declaration removed after integration'})
assert len(changes)==15
least=[x for x in changes if x['declaration'] not in ['computesFunInTime_pairDup_spaceUsed','computesFunInTime_incFixed_spaceUsed','redirectTM_spaceUsedByTape']];assert len(least)==12
file_rows=[];patch=''
for owner in sources:
 if proposed[owner]==sources[owner]:continue
 before=sources[owner];after=proposed[owner];f='TCSlib/Complexity/TuringMachine/'
 if owner in ['Loop','Primitives','Catalog','Wrappers']:f+='Build/'
 f+=owner+'.lean'
 (p/'inputs'/f'{owner}-baseline.lean.txt').write_text(before)
 (p/'inputs'/f'{owner}-after15-b1-REQUIRES-INTEGRATED-API119.lean.txt').write_text(after)
 patch+=''.join(difflib.unified_diff(before.splitlines(keepends=True),after.splitlines(keepends=True),fromfile='a/'+f,tofile='b/'+f))
 file_rows.append({'file':f,'before_sha256':H(before.encode()),'after_sha256':H(after.encode()),'bytes_before':len(before.encode()),'bytes_after':len(after.encode())})
assert len(file_rows)==6
(p/'all15-bodies.patch').write_text(patch)
receipt={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'baseline':base,'status':'SOURCE-ONLY INERT15-change proposal; no actual source integration/compilation/seals/replay','changes_count':15,'least_entry_sites':12,'additional_since_original_six':9,'files':file_rows,'changes':changes,'all_imports_public_private_headers_attributes_runtime_machine_data_and_nontarget_bytes_frozen':True,'no_new_public_or_private_declarations':True,'all_twelve_old_least_entry_Nat_find_blocks_replaced_in_proposal':True,'no_new_API_import_host_statement_or_debt':'No extra design choice identified; hfix for fwdMap_launch follows existing same-home stationary contract via published run equations','integration_warning':'Do NOT overwrite integrated files with saved b1-relative whole-source copies; integrate complete mergedAPI119first, preserve publisher additions, then apply scoped hunks. Check conflicts, actual native chain, all newly changed-region seals/controls, sourcefreeze,metadata/screens and merged-tree replay before proposing clearance.','native_evidence_limit':'Only original generation1 generic3headers+2spaceleaves native/sealed+14controls. All9additional production rewrites—including seventh—are SOURCE ONLY; retained legacy remainder may require mechanical reader repairs in actual strong seals. No claimed whole-family/audit closure.'}
(p/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'changes':[(x['file'],x['declaration']) for x in changes],'files':file_rows},indent=2))
