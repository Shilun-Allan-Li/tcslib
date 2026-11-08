from pathlib import Path
import json,re,hashlib
O=Path('/private/tmp/ab34-ro1-integration');W=Path('/Users/seyoonr/.codex/worktrees/ab34-sg1/tcslib-arora-barak-ch3-4')
changes={};rows=[]
def exact(rel,old,new,kind='additional exact inline conversion',n=1):
    p='TCSlib/Complexity/'+rel+'.lean';s=changes.get(p,(W/p).read_text());assert s.count(old)==n,(p,old,s.count(old),n)
    for m in re.finditer(re.escape(old),s):rows.append({'path':p,'line_at_revision2':s.count('\n',0,m.start())+1,'kind':kind,'before':old,'after':new})
    changes[p]=s.replace(old,new)
exact('ClassP/TimeConstructible','simp only [counterCarry, MultiTapeTM.runFrom_one, counter_carry_step]',
      'simp only [counterCarry]\n    rw [MultiTapeTM.runFrom_one, counter_carry_step]','repair simp matcher at zero-plus-one',1)
# The false branch has two additional spaces of indentation.
exact('ClassP/TimeConstructible','simp only [counterCarry, MultiTapeTM.runFrom_one, counter_carry_step]',
      'simp only [counterCarry]\n      rw [MultiTapeTM.runFrom_one, counter_carry_step]','repair simp matcher at zero-plus-one',1)
exact('ClassP/TimeConstructible','simp only [MultiTapeTM.runFrom_one]','rw [MultiTapeTM.runFrom_one]','repair simp matcher at zero-plus-one')
exact('TuringMachine/Build/InputWindow',
      "  calc\n    _ = M.step (M.runFrom c 0) := MultiTapeTM.runFrom_succ_eq_step'\n    _ = _ := by rw [MultiTapeTM.runFrom_zero, MultiTapeTM.step_of_some hc]",
      '  rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_some hc]','separated calc one-step proof')
exact('TuringMachine/Build/Loop',
      '  change (emCallTrackTM M).tm.step ((emCallTrackTM M).tm.initCfg x) = _',
      '  rw [MultiTapeTM.runFrom_one]')
exact('TuringMachine/Build/Loop','    change (controlAction 0 (some (5 : Fin 6))).apply c = c',
      '    rw [MultiTapeTM.runFrom_one]\n    change (controlAction 0 (some (5 : Fin 6))).apply c = c')
exact('TuringMachine/Build/OracleSim','    change oracleDispatchTM.step localInit = _',
      '    rw [MultiTapeTM.runFrom_one]')
exact('TuringMachine/Build/Primitives',
      '  refine ⟨he, ?_⟩\n  intro j hj\n  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl\n  · exact hc\n  · change (tm.step c).state ≠ _\n    rw [he]; exact hd',
      '  refine ⟨(MultiTapeTM.runFrom_one tm c).trans he, ?_⟩\n  intro j hj\n  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl\n  · exact hc\n  · rw [MultiTapeTM.runFrom_one, he]\n    exact hd')
exact('TuringMachine/Build/Primitives','    change (controlAction 0 (some (.prepare (0, false)))).apply z = p',
      '    rw [MultiTapeTM.runFrom_one]\n    change (controlAction 0 (some (.prepare (0, false)))).apply z = p')
exact('TuringMachine/Build/Primitives','      change host.step z = (embedEmitCfg index tapes heads [] (src.step c)).mapState emb',
      '      rw [MultiTapeTM.runFrom_one, MultiTapeTM.runFrom_one]')
exact('TuringMachine/Build/Primitives','      change ((embedEmitTM index src).step ec).mapState emb =',
      '      simp only [MultiTapeTM.runFrom_one] at r1\n      change ((embedEmitTM index src).step ec).mapState emb =')
exact('TuringMachine/Build/Primitives','    change tm.step z = p','    rw [MultiTapeTM.runFrom_one]')
exact('TuringMachine/Build/RecordTable','    change (rt_boundaryTM k i b).step d = a','    rw [MultiTapeTM.runFrom_one]')
exact('TuringMachine/Build/StepBlock',
      '    have he : (seekTM k).runFrom (seekCfg d (.state rank)) 1 = seekCfg d .done := step',
      '    have he : (seekTM k).runFrom (seekCfg d (.state rank)) 1 = seekCfg d .done := by\n      rw [MultiTapeTM.runFrom_one]\n      exact step')
exact('TuringMachine/Build/StepBlockForward','fl_flush (if live then some none else none) d := fl_leaf_step d live hd',
      'fl_flush (if live then some none else none) d := by\n  rw [MultiTapeTM.runFrom_one]\n  exact fl_leaf_step d live hd')
exact('TuringMachine/CodeSimulator','      simpa only [moveInputPos_zero] using step',
      '      rw [MultiTapeTM.runFrom_one]\n      simpa only [moveInputPos_zero] using step')
exact('TuringMachine/CodeSimulator',
      '        inputPos := moveInputPos d.inputPos (if d.inputSymbol.isSome then 1 else 0) } :=\n  step_of_inputMoveAction _ _ _ hs rfl',
      '        inputPos := moveInputPos d.inputPos (if d.inputSymbol.isSome then 1 else 0) } := by\n  rw [MultiTapeTM.runFrom_one]\n  exact step_of_inputMoveAction _ _ _ hs rfl')
exact('TuringMachine/CodeSimulator','    have step : (canonSuffixTM m).runFrom d 1 = e :=\n      step_of_inputMoveAction _ _ _ state (by simp [canonSuffixTM, read, tail])',
      '    have step : (canonSuffixTM m).runFrom d 1 = e := by\n      rw [MultiTapeTM.runFrom_one]\n      exact step_of_inputMoveAction _ _ _ state (by simp [canonSuffixTM, read, tail])')
exact('TuringMachine/CodeSimulator','simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, hs, canonHaltTM, Action.apply]',
      'simp [MultiTapeTM.runFrom_one, MultiTapeTM.step, hs, canonHaltTM, Action.apply]','one-step simp successor implicit zero')
exact('SpaceComplexity/Inclusions',"simp [M, b2b_answerTM, MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step, hc,",
      'simp [M, b2b_answerTM, MultiTapeTM.runFrom_one, MultiTapeTM.step, hc,','one-step simp successor implicit zero')
exact('CircuitComplexity/MeyerMachineSetup',
      'rw [MultiTapeTM.runFrom_succ_eq_step, List.length_nil, MultiTapeTM.runFrom_zero,',
      'rw [List.length_nil, MultiTapeTM.runFrom_one,','separated nil-length successor/zero pair')
exact('CircuitComplexity/MeyerMachineSetup',
      '      MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step,\n      pcfg_fA M f bits p h1 (by omega) e r0,',
      '      MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_one,\n      pcfg_fA M f bits p h1 (by omega) e r0,','inner one-step of two-step chain')
exact('CircuitComplexity/MeyerMachineSetup','      pcfg_fB_false M f e bits (p + 1) (by omega) (by omega) r1, MultiTapeTM.runFrom_zero]',
      '      pcfg_fB_false M f e bits (p + 1) (by omega) (by omega) r1]','remove discharged zero after inner one-step')

R=O/'revision2';assert not R.exists();R.mkdir()
for p,s in changes.items():
    original=(W/p).read_text();before=R/'before'/(p+'.txt');before.parent.mkdir(parents=True,exist_ok=True);before.write_text(original)
    after=R/'after'/(p+'.txt');after.parent.mkdir(parents=True,exist_ok=True);after.write_text(s)
for p,s in changes.items():(W/p).write_text(s)
(R/'edits.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
print('revision2 rows',len(rows),'owners',len(changes))
