from pathlib import Path
O=Path(__file__).parent;P=O/'project'
head='''import TCSlib.Complexity.TuringMachine.Simulation
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
open Turing
attribute [-simp] Turing.Action.apply
'''
body='''example {k : ℕ} {State : Type} {input : List Bool}
    (cfg : Cfg k Bool State input) (b : Bool) (hout : cfg.output = []) :
    (Action.mk 0 (fun _ => (none, 0)) (some b) none).apply cfg =
      {cfg with state := none, output := [b]} := by
  apply Cfg.ext
  · rw [Action.apply_state]
  · rw [Action.apply_inputPos, moveInputPos_zero]
  · funext i
    rw [Action.apply_workTapes, Option.getD_none, Cfg.workTapeSymbols_eq, Function.update_eq_self]
  · funext i
    rw [Action.apply_workTapePos]
    change cfg.workTapePos i + (0 : ℤ) = cfg.workTapePos i
    exact add_zero _
  · rw [Action.apply_output, hout]
    rfl
'''
ctrl='''open Lean Elab Command Meta in
run_cmd do
  let targets : List Name := [`Turing.Action.apply, `Turing.Cfg.workTapeSymbols, `Turing.moveInputPos]
  let mut i := 0
  for name in targets do
    let some (.defnInfo info) := (← getEnv).find? name | throwError "not ordinary definition {name}"
    for mode in ["point", "abstract"] do
      i := i + 1
      let result ← liftTermElabM do
        let levels := info.levelParams.map Level.param
        let head := mkConst name levels
        let solve := fun (lhs rhs : Expr) => do
          let ty ← mkEq lhs rhs
          let goal ← mkFreshExprSyntheticOpaqueMVar ty
          try
            goal.mvarId!.refl
            pure (some (ty, ← instantiateMVars goal))
          catch ex =>
            logInfo m!"READER_CONTROL|{name}|{mode}|FAIL"
            logError m!"READER_RFL|{name}|{mode}|{ex.toMessageData}"
            pure none
        if mode == "abstract" then solve head info.value
        else forallTelescope info.type fun xs _ => solve (mkAppN head xs) ((mkAppN info.value xs).headBeta)
      if let some (ty, value) := result then
        let kernelName := Name.mkSimple ("FE1ReaderControl_" ++ toString i)
        liftCoreM <| addDecl (.thmDecl { name := kernelName, levelParams := info.levelParams, type := ty, value := value })
        logInfo m!"READER_CONTROL|{name}|{mode}|PASS|kernelChecked={kernelName}"
'''
for side in ['native','sealed']:
 attr='' if side=='native' else 'attribute [local irreducible] Turing.Action.apply Turing.Cfg.workTapeSymbols Turing.moveInputPos\n'
 for label,source in [('ActionReader',body),('ReaderControls',ctrl)]:
  text=head+attr+source;f=P/('FE1'+label+'_'+side+'.lean');f.write_text(text);(O/'reader-probes').mkdir(exist_ok=True);(O/'reader-probes'/(f.name+'.txt')).write_text(text)
