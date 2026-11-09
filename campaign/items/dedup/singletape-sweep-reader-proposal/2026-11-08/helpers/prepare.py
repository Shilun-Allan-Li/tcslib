from pathlib import Path
import subprocess,os,tarfile,io,json,hashlib,re,difflib
O=Path(__file__).parent;E=O/'evidence';R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');S=Path(os.environ['TCSLIB_SCRATCH']);HEAD='f3c8c050ef98375bc237c72bde74f83d33833374';BASE='9b5dcf46408db681bcbc721930ef2203fa6bc47d';env=os.environ|{'GIT_OPTIONAL_LOCKS':'0'};W=O/'runtime/project';OV=O/'runtime/oleans-proposal';W.mkdir(parents=True)
H=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(R),*args],env=env)
def save(n,a):(E/n).write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n')
paths=[p for p in git('ls-tree','-r','--name-only',HEAD).decode().splitlines() if p.endswith('.lean')];assert len(paths)==1003
archive=git('archive',HEAD,*paths,'lean-toolchain','lake-manifest.json');inventory=[]
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
 for m in tar.getmembers():
  p=Path(m.name);assert not p.is_absolute() and '..' not in p.parts
  if m.isdir():continue
  assert m.isfile();data=tar.extractfile(m).read();q=W/p;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(data);inventory.append({'path':m.name,'bytes':len(data),'sha256':H(data)})
(W/'.lake').mkdir();(W/'.lake/packages').symlink_to(R/'.lake/packages',target_is_directory=True);(E/'helpers').mkdir()
for name in ['leanelab.sh','leanelab-o.sh']:(E/'helpers'/name).write_bytes((R/'devtools/seyoon'/name).read_bytes())
for name in ['lean-toolchain','lake-manifest.json']:(E/'helpers'/name).write_bytes((W/name).read_bytes())
owner='TCSlib/Complexity/TuringMachine/Sweep.lean';consumer='TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean';obase=(W/owner).read_text();cbase=(W/consumer).read_text();assert git('show',BASE+':'+owner).decode()==obase and git('show',BASE+':'+consumer).decode()==cbase
search=[]
for path in paths:
 for i,l in enumerate((W/path).read_text().splitlines(),1):
  if 'sweepRevCfg' in l:search.append({'path':path,'line':i,'text':l})
save('EXISTING-READER-SEARCH.json',{'source':HEAD,'source_population':1003,'all_raw_candidates':search,'initial_disposition':'Existing sweepRevCfg_left and sweepRevCfg_left_any are action/transition contracts, not the state/output field equations needed by these complete consumers. No equivalent public standalone state/output reader located. Work-head reader not introduced because existing DGSpan already carries required final head bounds. Search plus inspection, not semantic exhaustive absence.'})
state=r'''/-- The reverse-sweep configuration has the supplied control state. -/
theorem sweepRevCfg_state {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    (sweepRevCfg q p z l r out).state = q := by
  rfl
'''
output=r'''/-- The reverse-sweep configuration has the supplied output word. -/
theorem sweepRevCfg_output {A S : Type} {x : List A} (q : Option S)
    (p : Fin (x.length + 2)) (z : ℤ) (l r : List (Option A)) (out : List A) :
    (sweepRevCfg q p z l r out).output = out := by
  rfl
'''
marker='/-- Reflection converts the forward zipper identity into a left-moving step. -/';assert obase.count(marker)==1;ocand=obase.replace(marker,state+'\n'+output+'\n'+marker);assert ocand.replace(state+'\n'+output+'\n','')==obase;(W/owner).write_text(ocand)
a=cbase.index('/-- **One work tape suffices**');b=cbase.index('/-- One work tape and the binary alphabet',a);one=cbase[a:b];newone=one.replace('  by_cases hk : M.k = 0','  have hFun := (computesFunInTime_iff M f T).mp hM\n  by_cases hk : M.k = 0',1);assert newone.count('    intro x')==2;newone=newone.replace('    intro x','    apply (computesFunInTimeVia_iff _ _ _ _).mpr\n    intro x');s='      ((unusedTape_computes M hk f T hM) x).mono';t='      (((computesFunInTime_iff _ _ _).mp\n        (unusedTape_computes M hk f T hM)) x).mono';assert newone.count(s)==1;newone=newone.replace(s,t).replace('.mp (hM x)','.mp (hFun x)');start=newone.index('    have hex :');stop=newone.index('    have hrun :=',start);newone=newone[:start]+'''    obtain ⟨τ, ht, hlive, hfirst⟩ :=
      MultiTapeTM.exists_first_halt M.tm (M.tm.initCfg x) hhalt
    have hτ : (M.tm.runFrom (M.tm.initCfg x) τ).state = none :=
      (congrArg Cfg.state hfirst).trans hhalt
'''+newone[stop:];start=newone.index('    have houtτ :');stop=newone.index('    have hc :',start);newone=newone[:start]+'''    have houtτ : (M.tm.runFrom (M.tm.initCfg x) τ).output = f x :=
      (congrArg Cfg.output hfirst).trans hout
'''+newone[stop:];s='''      · change (M.tm.runFrom (M.tm.initCfg x) τ).state.map (fun q => SweepState.growLeft q 0) = none
        rw [hτ]
        rfl
      · change (M.tm.runFrom (M.tm.initCfg x) τ).output.map (sweepEmbed Γ M.k) = _
        rw [houtτ]''';t='''      · simp only [sweepStart, sweepRevCfg_state, hτ, Option.map_none]
      · rw [sweepStart, sweepRevCfg_output, houtτ]''';assert newone.count(s)==1;newone=newone.replace(s,t)
a2=cbase.index('/-- The demand-grown witness computes on every native word');b2=cbase.index('/-- The one-work-tape reduction preserves space',a2);dg=cbase[a2:b2];newdg=dg.replace('  let y :=','  have hFun := (computesFunInTime_iff M f T).mp hM\n  let y :=',1).replace('.mp (hM y)','.mp (hFun y)');start=newdg.index('  have hex :');stop=newdg.index('  obtain ⟨a, n, u, window',start);newdg=newdg[:start]+'''  obtain ⟨τ, htime, hlive, hfirst⟩ :=
    MultiTapeTM.exists_first_halt M.tm (M.tm.initCfg y) hhalt
  have hτ : (M.tm.runFrom (M.tm.initCfg y) τ).state = none :=
    (congrArg Cfg.state hfirst).trans hhalt
'''+newdg[stop:];s='''    (M.tm.runFrom_output_eq_of_halt (M.tm.initCfg y) htime hτ).symm.trans hout''';t='''    (congrArg Cfg.output hfirst).trans hout''';assert newdg.count(s)==1;newdg=newdg.replace(s,t);s='''    change (M.tm.runFrom (M.tm.initCfg y) τ).state.map _ = none
    rw [hτ]
    rfl''';t='''    simp only [final, dgStart, sweepRevCfg_state, hτ, Option.map_none]''';assert newdg.count(s)==1;newdg=newdg.replace(s,t);s='''    · change (M.tm.runFrom (M.tm.initCfg y) τ).output.map (sweepEmbed Γ M.k) = _
      rw [houtτ]''';t='''    · rw [dgStart, sweepRevCfg_output, houtτ]''';assert newdg.count(s)==1;newdg=newdg.replace(s,t);s='''      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hj''';t='''      obtain ⟨s, _, rfl⟩ :=
        (MultiTapeTM.mem_visitedByTapeHead_iff (tm := (dgTM M a₀).tm)
          ((dgTM M a₀).tm.initCfg x) v (0 : Fin 1) j).mp hj''';assert newdg.count(s)==1;newdg=newdg.replace(s,t);s='''      change (∑ i : Fin 1, ((dgTM M a₀).tm.visitedByTapeHead ((dgTM M a₀).tm.initCfg x) v i).card) ≤ _''';t='''      rw [MultiTapeTM.spaceUsed_eq_sum]''';assert newdg.count(s)==1;newdg=newdg.replace(s,t);s='''      rw [← hcard]''';t='''      rw [MultiTapeTM.spaceUsedByTape_eq_card, ← hcard]''';assert newdg.count(s)==1;newdg=newdg.replace(s,t)
header=lambda s:s[:s.index(':= by\n')+len(':= by\n')];assert header(one)==header(newone) and header(dg)==header(newdg);ccand=cbase.replace(one,newone).replace(dg,newdg);assert cbase.count(one)==1 and cbase.count(dg)==1;(W/consumer).write_text(ccand)
for path,base,cand in [(owner,obase,ocand),(consumer,cbase,ccand)]:
 for side,text in [('BASE-f3',base),('CANDIDATE',cand)]:
  p=E/'source'/side/(path+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
for name,text in [('proposed-state-reader',state),('proposed-output-reader',output),('one_work_tape-BASE',one),('one_work_tape-CANDIDATE',newone),('dg_all_inputs-BASE',dg),('dg_all_inputs-CANDIDATE',newdg)]: (E/(name+'.lean.txt')).write_text(text)
def patch(old,new,path):return ''.join(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),fromfile='a/'+path,tofile='b/'+path))
api=patch(obase,ocand,owner);cons=patch(cbase,ccand,consumer);(E/'API-only.patch').write_text(api);(E/'both-consumers.patch').write_text(cons);(E/'one_work_tape-only.patch').write_text(patch(cbase,cbase.replace(one,newone),consumer));(E/'dg_all_inputs-only.patch').write_text(patch(cbase,cbase.replace(dg,newdg),consumer));(E/'combined-proposal.patch').write_text(api+cons)
subprocess.run(['cp','-cR',str(S/'oleans-mac8'),str(OV)],check=True)
def objects(root):return {str(p.relative_to(root)):H(p.read_bytes()) for p in sorted((root/'TCSlib').rglob('*.olean'))}
a=objects(S/'oleans-mac8');b=objects(OV);assert len(a)==895 and a==b==json.loads((R/'campaign/status/2026-11-08-mig1-merge/object-hashes.json').read_text());save('INPUT895-original.json',a);save('INPUT895-clone-before.json',b);save('SOURCE1003-f3.json',inventory);save('SOURCE-BINDING.json',{'source_f3':HEAD,'snapshot_MAC8':BASE,'producer':owner,'consumer':consumer,'new_public_API_hypotheses':['Turing.FinTM.sweepRevCfg_state','Turing.FinTM.sweepRevCfg_output'],'both_original_owners_BASE_f3_exact':True,'no_work_head_reader_added_unless_needed':True,'all_old_definitions_imports_headers_attributes_other_source_literal_exact':True,'no_gate129_core_ND_API_dependency':True,'one_own_Lean_job_at_a_time':True,'localcap':3,'machinecap':5});print('Prepared two field-reader hypotheses and both complete SingleTape consumer candidates, exact BASE/f3 source, wholeMAC8 private clone.')
