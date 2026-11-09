from pathlib import Path
import os,subprocess,tarfile,io,json,hashlib,difflib,re
O=Path(__file__).parent;E=O/'evidence';R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');S=Path(os.environ['TCSLIB_SCRATCH']);D64='d64dff4fbef865d815c6a561ce8037ea1bae07a2';BASE='9b5dcf46408db681bcbc721930ef2203fa6bc47d';env=os.environ|{'GIT_OPTIONAL_LOCKS':'0'};W=O/'runtime/project';OV=O/'runtime/oleans-proposal';W.mkdir(parents=True)
H=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git','-C',str(R),*args],env=env)
def save(n,a):(E/n).write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n')
paths=[p for p in git('ls-tree','-r','--name-only',D64).decode().splitlines() if p.endswith('.lean')];assert len(paths)==1003
archive=git('archive',D64,*paths,'lean-toolchain','lake-manifest.json');rows=[]
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
 for m in tar.getmembers():
  p=Path(m.name);assert not p.is_absolute() and '..' not in p.parts
  if m.isdir():continue
  assert m.isfile();data=tar.extractfile(m).read();f=W/p;f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes(data);rows.append({'path':m.name,'bytes':len(data),'sha256':H(data)})
(W/'.lake').mkdir();(W/'.lake/packages').symlink_to(R/'.lake/packages',target_is_directory=True);(E/'helpers').mkdir()
for name in ['leanelab.sh','leanelab-o.sh']:(E/'helpers'/name).write_bytes((R/'devtools/seyoon'/name).read_bytes())
for name in ['lean-toolchain','lake-manifest.json']:(E/'helpers'/name).write_bytes((W/name).read_bytes())
# The runner was read before reuse and executes only one helper job per call.
p=Path('/private/tmp/ab34-inputlength-three-reader-proposal/evidence/tools/run_one.py');runner=p.read_text().replace('whole complete895 MAC8 clone with sequential hypothetical Simulation/Catalog/Scan reader compilations, no snapshot composition','whole complete895 MAC8 clone; only comparator Hardness owner compilation; no proposed public API');(O/'run_one.py').write_text(runner)
path='TCSlib/Complexity/CookLevin/Hardness.lean';original=(W/path).read_text();token='private lemma clA5Compare_compute';start=original.index(token);doc=original.rfind('/--',0,start);stop=original.index('\n/-- Native equality of two binary natural-number words',start);old=original[doc:stop];header=old[:old.index(':= by\n')+len(':= by\n')];new=old
s='''  have init : Cfg.ofWords (input := arg) clCmpTM.tm.q₀ w =
      clCmpCfg arg 1 (.inl (false, false, true)) w 0 := rfl'''
t='''  have init : Cfg.ofWords (input := arg) clCmpTM.tm.q₀ w =
      clCmpCfg arg 1 (.inl (false, false, true)) w 0 := by
    apply Cfg.ext
    · exact Cfg.ofWords_state _ _
    · exact Cfg.ofWords_inputPos _ _
    · funext i
      exact Cfg.ofWords_workTapes _ _ i
    · funext i
      exact Cfg.ofWords_workTapePos _ _ i
    · exact Cfg.ofWords_output _ _'''
assert new.count(s)==1;new=new.replace(s,t)
a=new.index('  obtain ⟨t, ht, hp, hf, hr⟩ := clFirst');b=new.index('  have actionid',a)
t='''  have resultState : result.state = some (ret b) := by
    dsimp only [result, clPreparedCfg]
    rw [clPlacedCfg_eq]
    rfl
  obtain ⟨t, ht, hcut, hr⟩ := MultiTapeTM.exists_first_entry_of_fixed
    A.tm (fun q => ∃ v : Bool, q = ret v) (A.tm.initCfg arg) result
    (a + (2 * clCmpSize w + 2))
    (by
      rintro cfg ⟨q, hq, v, rfl⟩
      exact idle v cfg hq)
    ⟨ret b, resultState, b, rfl⟩ hend
  have guard : ∀ j < t, ∀ v, (A.tm.runFrom (A.tm.initCfg arg) j).state ≠ some (ret v) := by
    intro j hj v hv
    exact hcut j hj ⟨ret v, hv, v, rfl⟩
''';new=new[:a]+t+new[b:]
s='''  have actionid (act : Action A.k Bool A.State) : Action.mapState id act = act := by
    delta Action.mapState
    simp only [Option.map_id]
    rfl'''
t='''  have actionid (act : Action A.k Bool A.State) : Action.mapState id act = act := by
    change Action.mk (act.mapState id).inputTape (act.mapState id).workTapes
      (act.mapState id).output (act.mapState id).state = act
    have hw : (act.mapState id).workTapes = act.workTapes := by
      funext i
      exact Action.mapState_workTapes id act i
    rw [Action.mapState_inputTape, hw, Action.mapState_output,
      Action.mapState_state, Option.map_id]
    rfl''';assert new.count(s)==1;new=new.replace(s,t)
s='''  have mapid (cfg : Cfg A.k Bool A.State arg) : cfg.mapState id = cfg := by
    cases cfg
    simp [Cfg.mapState]'''
t='''  have mapid (cfg : Cfg A.k Bool A.State arg) : cfg.mapState id = cfg := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, Option.map_id]
      rfl
    · exact Cfg.mapState_inputPos id cfg
    · funext i z
      rw [Cfg.mapState_workTapes]
    · funext i
      rw [Cfg.mapState_workTapePos]
    · exact Cfg.mapState_output id cfg''';assert new.count(s)==1;new=new.replace(s,t)
s='  have hi : A.tm.initCfg arg = clA5CompareTM.tm.initCfg arg := rfl';t='''  have hi : A.tm.initCfg arg = clA5CompareTM.tm.initCfg arg := by
    rw [MultiTapeTM.initCfg_eq, MultiTapeTM.initCfg_eq]
    rfl''';assert new.count(s)==1;new=new.replace(s,t)
s='''  have finish : clA5CompareTM.tm.step result = {result with state := none, output := [b]} := by
    change (Action.mk 0 (fun _ => (none, 0)) (some b) none).apply result = _
    simp [Action.apply, show result.output = [] from rfl]'''
t='''  have finish : clA5CompareTM.tm.step result = {result with state := none, output := [b]} := by
    have fields : result.state = some (ret b) ∧ result.output = [] := by
      dsimp only [result, clPreparedCfg]
      rw [clPlacedCfg_eq]
      exact ⟨rfl, rfl⟩
    rw [MultiTapeTM.step_of_some fields.1]
    change (Action.mk 0 (fun _ => (none, 0)) (some b) none).apply result = _
    apply Cfg.ext
    · rw [Action.apply_state]
    · rw [Action.apply_inputPos, moveInputPos_zero]
    · funext i
      rw [Action.apply_workTapes, Option.getD_none, Cfg.workTapeSymbols_eq,
        Function.update_eq_self]
    · funext i
      rw [Action.apply_workTapePos]
      change result.workTapePos i + (0 : ℤ) = result.workTapePos i
      exact add_zero _
    · rw [Action.apply_output, fields.2]
      rfl''';assert new.count(s)==1;new=new.replace(s,t)
assert new.startswith(header);candidate=original[:doc]+new+original[stop:];(W/path).write_text(candidate)
for rel,text in [('source/BASE-d64/'+path+'.txt',original),('source/CANDIDATE/'+path+'.txt',candidate),('target/BASE.lean.txt',old),('target/CANDIDATE.lean.txt',new)]:
 p=E/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
(E/'proposal.patch').write_text(''.join(difflib.unified_diff(original.splitlines(keepends=True),candidate.splitlines(keepends=True),fromfile='a/'+path,tofile='b/'+path)))
subprocess.run(['cp','-cR',str(S/'oleans-mac8'),str(OV)],check=True)
def objects(root):return {str(p.relative_to(root)):H(p.read_bytes()) for p in sorted((root/'TCSlib').rglob('*.olean'))}
a=objects(S/'oleans-mac8');b=objects(OV);assert a==b==json.loads((R/'campaign/status/2026-11-08-mig1-merge/object-hashes.json').read_text()) and len(a)==895
save('INPUT895-original.json',a);save('INPUT895-clone-before.json',b);save('SOURCE1003-d64.json',rows);save('SOURCE-BINDING.json',{'source_HEAD':D64,'snapshot_BASE':BASE,'path':path,'original_sha256':H(original.encode()),'candidate_sha256':H(candidate.encode()),'original_full_target_sha256':H(old.encode()),'candidate_full_target_sha256':H(new.encode()),'complete_original_doc_header_exact':True,'only_one_existing_private_proof_changed':True,'all_preceding_and_following_owner_source_literal_exact':True,'no_new_API_import_header_definition_attribute':True,'no_three_proposed_readers_dependency':True,'root_name':'_private.TCSlib.Complexity.CookLevin.Hardness.0.Complexity.clA5Compare_compute','whole_overlay_objects':895,'localcap':3,'machinecap':5,'one_own_Lean_job_at_a_time':True})
print('Prepared exact d64 full-owner comparator candidate, sole proof change, fresh wholeMAC8 clone.')
