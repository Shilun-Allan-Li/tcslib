from pathlib import Path
import json,re,difflib,hashlib,shutil
O=Path(__file__).parent;R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4');rows=json.loads((O/'candidate-declarations.json').read_text());targets={d['name']:d for d in rows if d['id'] in [10,12,13,28,29,30,31,32,34,55,56]}
bodies={
'clBank_first':'''  let start := clBankCfg p (fun i => clCountCfg x (clBankStart (a i)) p 0 (n i).bits [])
  let finishCfg := clBankCfg p (fun i => clCountCfg x 0 p 0 (n i + if a i then 1 else 0).bits [])
  have finish : (clBankTM l).tm.runFrom start (2 * W + 2) = finishCfg :=
    clBank_finish x p a n W hW
  obtain ⟨t, ht, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed
    (clBankTM l).tm (fun q => q = (fun _ : Fin l => some (0 : Fin 4)))
    start finishCfg (2 * W + 2)
    (by
      rintro c ⟨q, hq, rfl⟩
      exact clBank_idle c hq)
    ⟨(fun _ => some (0 : Fin 4)), rfl, rfl⟩ finish
  exact ⟨t, ht, fun j hj hs => hcut j hj ⟨_, hs, rfl⟩, he⟩
''',
'clCopy_first':'''  have finish := clCopy_run x p w record
  obtain ⟨t, ht, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed
    clCopyTM.tm (fun q => q = (4 : Fin 5))
    (clCopyCfg x 0 p 0 w record) (clCopyCfg x 4 p 0 w (record ++ pairEncode w []))
    (3 * w.length + 3)
    (by
      rintro c ⟨q, hq, rfl⟩
      exact clCopy_idle c hq)
    ⟨(4 : Fin 5), rfl, rfl⟩ finish
  have hp : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    have hs := congrArg Cfg.state he
    rw [hz, MultiTapeTM.runFrom_zero] at hs
    have hh := congrArg (fun z => z.map Fin.val) hs
    norm_num [clCopyCfg] at hh
  exact ⟨t, ht, hp, fun j hj hs => hcut j hj ⟨(4 : Fin 5), hs, rfl⟩, he⟩
''',
'clRow_first':'''  obtain ⟨B, hB, finish⟩ := clRow_stored x p w record W hW
  obtain ⟨t, ht, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed
    (clRowTM l).tm (fun q => q = (Fin.last l, (0 : Fin 5)))
    (clRowCfg x p 0 0 w record)
    (clRowCfg x p (Fin.last l) 0 w (record ++ clRowPrefix w l)) B
    (by
      rintro c ⟨q, hq, rfl⟩
      exact clRow_idle c hq)
    ⟨(Fin.last l, 0), rfl, rfl⟩ finish
  have hp : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    have hs := congrArg Cfg.state he
    rw [hz, MultiTapeTM.runFrom_zero] at hs
    have hh := congrArg (fun z => z.map (fun q => q.1.val)) hs
    simp [clRowCfg] at hh
    omega
  exact ⟨t, ht.trans hB, hp, fun j hj hs => hcut j hj ⟨_, hs, rfl⟩, he⟩
''',
'clCmp_first':'''  let b := clCmpVerdict (clCmpOrbit w (clCmpSize w))
  have finish := clCmp_run x p w
  obtain ⟨t, ht, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed
    clCmpTM.tm (fun q => ∃ d : Bool, q = .inr (.inr d))
    (clCmpCfg x p (.inl (false, false, true)) w 0)
    (clCmpCfg x p (.inr (.inr b)) w 0) (2 * clCmpSize w + 2)
    (by
      rintro c ⟨q, hq, d, rfl⟩
      exact clCmp_idle c d hq)
    ⟨.inr (.inr b), rfl, b, rfl⟩ finish
  have hw : clCmpSize w ≤ W := Finset.sup_le (fun i _ => hW i)
  have hp : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    have hh := congrArg Cfg.state he
    rw [hz, MultiTapeTM.runFrom_zero] at hh
    cases hh
  exact ⟨t, by omega, hp, b, clCmpVerdict_spec w,
    fun j hj d hd => hcut j hj ⟨.inr (.inr d), hd, d, rfl⟩, he⟩
''',
'clFirst':'''  obtain ⟨t, ht, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed
    tm (fun q => q = ret) start finish B
    (by
      rintro c ⟨q, hq, rfl⟩
      exact hidle c hq)
    ⟨ret, hret, rfl⟩ hrun
  have hp : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    have hs := congrArg Cfg.state he
    rw [hz, MultiTapeTM.runFrom_zero, hret] at hs
    exact hstart hs
  exact ⟨t, ht, hp, fun j hj hs => hcut j hj ⟨ret, hs, rfl⟩, he⟩
''',
'xr_firstArrival':'''  obtain ⟨t, ht, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed
    tm (fun q => q = a) c c' T
    (by
      rintro d ⟨q, hq, rfl⟩
      exact hstat d hq)
    ⟨a, hc', rfl⟩ h
  exact ⟨t, ht, he, fun u hu hs => hcut u hu ⟨a, hs, rfl⟩⟩
''',
"xr_firstArrival'":'''  obtain ⟨t, ht, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed
    tm A c c' T
    (by
      rintro d ⟨q, hq, hA⟩
      exact hstat d q hq hA)
    ⟨a, hc', ha⟩ h
  exact ⟨t, ht, he, fun u hu a' ha' hA => hcut u hu ⟨a', ha', hA⟩⟩
''',
'enumCont_first_anchor':'''  obtain ⟨t, ht, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed
    stop (fun q => q = qa) c (stop.runFrom c T) T
    (by
      rintro d ⟨q, hq, hqa⟩
      have hstate : d.state = some qa := hq.trans (congrArg some hqa)
      simpa only [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero] using
        enumCont_absorb stop qa hs d hstate 1)
    ⟨qa, hT, rfl⟩ rfl
  have hn : ∀ j < t, (stop.runFrom c j).state ≠ some qa :=
    fun j hj hs => hcut j hj ⟨qa, hs, rfl⟩
  refine ⟨t, ht, ?_, ?_⟩
  · intro j hj
    rw [enumCont_agree_run tm stop qa ha c j (fun i hi => hn i (by omega))]
    exact hn j hj
  · rw [enumCont_agree_run tm stop qa ha c t hn]
    exact he
'''}
# Additional non-Nat.find first-entry closings.
bodies['inputSeekRewind_run'] = """  obtain ⟨r, hr, hrun, hheads⟩ := FinTM.rewind_heads inputSeekRewind .start .scan
    (some .left) (fun _ _ => rfl) (fun inp _ => by cases inp <;> rfl) d hd
  have hend : inputSeekRewind.runFrom d (r + 1) =
      { d with state := some .done, inputPos := 0 } := by
    rw [MultiTapeTM.runFrom_succ_eq_step', hrun, MultiTapeTM.step_of_some rfl]
    change (FinTM.controlAction SignType.neg (some InputSeekRw.done)).apply
      ({ d with state := some .left, inputPos := 1 } : Cfg 2 Bool InputSeekRw x) = _
    rw [FinTM.controlAction_apply]
    apply Cfg.ext rfl _ rfl rfl rfl
    apply Fin.ext
    rw [FinTM.moveInputPos_neg_val]
  obtain ⟨u, hu, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed
    inputSeekRewind (fun q => q = .done) d {d with state := some .done, inputPos := 0} (r + 1)
    (by
      rintro z ⟨q, hq, rfl⟩
      rw [MultiTapeTM.step_of_some hq]
      change (FinTM.controlAction 0 (some InputSeekRw.done)).apply z = z
      rw [FinTM.controlAction_apply, moveInputPos_zero]
      cases z
      simp_all)
    ⟨.done, rfl, rfl⟩ hend
  refine ⟨u, by omega, he, (fun v hv hs => hcut v hv ⟨.done, hs, rfl⟩), ?_⟩
  intro v hv
  have hvr : v ≤ r + 1 := hv.trans hu
  by_cases hvr' : v ≤ r
  · exact hheads v hvr'
  · have : v = r + 1 := by omega
    subst v
    rw [hend]
"""
cmp=targets['clA5Compare_compute'];cmpold=(O/cmp['block']).read_text();oldguard="""  have guard : ∀ j < t, ∀ v, (A.tm.runFrom (A.tm.initCfg arg) j).state ≠ some (ret v) := by
    intro j hj v hv
    have stay := Function.iterate_fixed (idle v _ hv) (t - j)
    change A.tm.runFrom (A.tm.runFrom (A.tm.initCfg arg) j) (t - j) =
      A.tm.runFrom (A.tm.initCfg arg) j at stay
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_of_le (by omega), hr] at stay
    have hstate := congrArg Cfg.state stay
    change some (ret b) = _ at hstate
    rw [hv] at hstate
    have hb : b = v := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Option.some.inj hstate)))
    exact hf j hj (by rw [hb]; exact hv)
""";newguard="""  have guard : ∀ j < t, ∀ v, (A.tm.runFrom (A.tm.initCfg arg) j).state ≠ some (ret v) := by
    have resultState : result.state = some (ret b) := by
      dsimp only [result, clPreparedCfg]
      rw [clPlacedCfg_eq]
      rfl
    obtain ⟨u, hu, hcut, he⟩ := MultiTapeTM.exists_first_entry_of_fixed
      A.tm (fun q => ∃ v : Bool, q = ret v) (A.tm.initCfg arg) result t
      (by
        rintro cfg ⟨q, hq, v, rfl⟩
        exact idle v cfg hq)
      ⟨ret b, resultState, b, rfl⟩ hr
    have hut : u = t := by
      apply Nat.le_antisymm hu
      by_contra hn
      have hult : u < t := by omega
      apply hf u hult
      exact (congrArg Cfg.state he).trans resultState
    subst u
    intro j hj v hv
    exact hcut j hj ⟨ret v, hv, v, rfl⟩
""";assert cmpold.count(oldguard)==1;bodies['clA5Compare_compute']=cmpold.replace(oldguard,newguard).split(':= by\n',1)[1]

# Complete-declaration core-step seal exposes the inherited final emission reader.
finishOld="""  have finish : clA5CompareTM.tm.step result = {result with state := none, output := [b]} := by
    change (Action.mk 0 (fun _ => (none, 0)) (some b) none).apply result = _
    simp [Action.apply, show result.output = [] from rfl]
"""
finishNew="""  have finish : clA5CompareTM.tm.step result = {result with state := none, output := [b]} := by
    have fields : result.state = some (ret b) ∧ result.output = [] := by
      dsimp only [result, clPreparedCfg]
      rw [clPlacedCfg_eq]
      exact ⟨rfl, rfl⟩
    rw [MultiTapeTM.step_of_some fields.1]
    change (Action.mk 0 (fun _ => (none, 0)) (some b) none).apply result = _
    apply Cfg.ext
    · rw [Action.apply_state]
      rfl
    · rw [Action.apply_inputPos, moveInputPos_zero]
    · funext i
      rw [Action.apply_workTapes]
      rfl
    · funext i
      rw [Action.apply_workTapePos]
      change result.workTapePos i + (0 : ℤ) = result.workTapePos i
      exact add_zero _
    · rw [Action.apply_output, fields.2]
      rfl
"""
assert bodies['clA5Compare_compute'].count(finishOld)==1
bodies['clA5Compare_compute']=bodies['clA5Compare_compute'].replace(finishOld,finishNew)

# InputLength's body retains all counting, return, framing and head-bound code except its inline cut.
inp=targets['exists_inputLengthTM'];old=(O/inp['block']).read_text();segment='''  -- Select the first exit, and use stationarity to keep the exact finish.
  have exits : ∃ u, (inputLengthMachine.runFrom d u).state = some .done :=
    ⟨t + 1 + r, congrArg Cfg.state finish⟩
  let first := Nat.find exits
  have firstState : (inputLengthMachine.runFrom d first).state = some .done :=
    Nat.find_spec exits
  have firstLe : first ≤ t + 1 + r := Nat.find_min' exits (congrArg Cfg.state finish)
  have fixed : inputLengthMachine.step (inputLengthMachine.runFrom d first) =
      inputLengthMachine.runFrom d first := by
    rw [step_of_inputMoveAction _ _ 0 firstState (q' := .done) rfl]
    simp only [moveInputPos_zero]
    apply Cfg.ext <;> simp [firstState]
  have same : inputLengthMachine.runFrom d (t + 1 + r) =
      inputLengthMachine.runFrom d first := by
    rw [show t + 1 + r = first + (t + 1 + r - first) by omega,
      MultiTapeTM.runFrom_add]
    exact Function.iterate_fixed fixed _
''';newseg='''  -- The public fixed-stop entry contract keeps the exact completed configuration.
  obtain ⟨first, firstLe, firstCut, firstEnd⟩ := MultiTapeTM.exists_first_entry_of_fixed
    inputLengthMachine (fun q => q = .done) d
    {back with state := some .done, inputPos := 1} (t + 1 + r)
    (by
      rintro z ⟨q, hq, rfl⟩
      rw [step_of_inputMoveAction _ _ 0 hq (q' := .done) rfl]
      simp only [moveInputPos_zero]
      apply Cfg.ext <;> simp [hq])
    ⟨.done, rfl, rfl⟩ finish
  have same : inputLengthMachine.runFrom d (t + 1 + r) =
      inputLengthMachine.runFrom d first := finish.trans firstEnd.symm
''';assert old.count(segment)==1;newold=old.replace(segment,newseg);guard='''    exact Nat.find_min exits hu
''';assert newold.count(guard)==1;newold=newold.replace(guard,'''    intro hs
    exact firstCut u hu ⟨.done, hs, rfl⟩
''');intro_old='''  · intro u hu
    intro hs
    exact firstCut u hu ⟨.done, hs, rfl⟩
''';intro_new='''  · intro u hu hs
    exact firstCut u hu ⟨.done, hs, rfl⟩
''';assert newold.count(intro_old)==1;newold=newold.replace(intro_old,intro_new);assert ':= by\n' in newold;bodies['exists_inputLengthTM']=newold.split(':= by\n',1)[1]
project=O/'project';project.mkdir(exist_ok=True);(project/'.lake').mkdir(exist_ok=True)
if not (project/'.lake/packages').exists():(project/'.lake/packages').symlink_to((R/'.lake/packages').resolve())
for p in ['lean-toolchain','lakefile.lean']:
 if (R/p).exists():shutil.copy2(R/p,project/p)
files={p:(O/'source'/(p+'.txt')).read_text() for p in {d['path'] for d in targets.values()}};mappings=[]
for name,d in targets.items():
 old=(O/d['block']).read_text();header=old.split(':= by\n',1)[0]+':= by\n';new=header+bodies[name]
 assert files[d['path']].count(old)==1,(name,'chunk binding')
 files[d['path']]=files[d['path']].replace(old,new)
 p=O/'draft-chunks'/f'{d["id"]:03d}-{name}.lean.txt';p.parent.mkdir(exist_ok=True);p.write_text(new)
 mappings.append({'path':d['path'],'name':name,'line':d['line'],'old_chunk':d['block'],'new_chunk':str(p.relative_to(O)),'header_exact':header==new.split(':= by\n',1)[0]+':= by\n','header_sha256':hashlib.sha256(header.encode()).hexdigest(),'old_chunk_sha256':hashlib.sha256(old.encode()).hexdigest(),'new_chunk_sha256':hashlib.sha256(new.encode()).hexdigest(),'new_body_sha256':hashlib.sha256(bodies[name].encode()).hexdigest(),'source_only_draft':True})
patch=[]
for path,new in sorted(files.items()):
 old=(O/'source'/(path+'.txt')).read_text();p=project/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(new);p2=O/'draft-source'/(path+'.txt');p2.parent.mkdir(parents=True,exist_ok=True);p2.write_text(new)
 patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 assert [x for x in old.splitlines() if x.startswith('import ')]==[x for x in new.splitlines() if x.startswith('import ')]
(O/'fe-live11-body-draft.patch').write_text(''.join(patch));(O/'DRAFT-SOURCE-MAP.json').write_text(json.dumps(mappings,ensure_ascii=False,indent=2)+'\n');print('draft roots',len(mappings),'files',len(files))
