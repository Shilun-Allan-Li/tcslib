from pathlib import Path
import json
O=Path(__file__).parent;defs=json.loads((O/'ORDINARY-UNION.json').read_text());heads=sorted(d['name'] for d in defs);simp=sorted(d['name'] for d in defs if d['simp'] or d['unfold']);top='''import Lean
import TCSlib.Complexity.TuringMachine.Simulation
import TCSlib.Complexity.TuringMachine.Build.Catalog
import TCSlib.Complexity.TuringMachine.Build.Scan
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option smartUnfolding false
set_option autoImplicit false
set_option relaxedAutoImplicit false
''';common=('attribute [-simp] '+' '.join(simp)+'\n') if simp else '';body='''open Lean Elab Command Meta in
run_cmd do
  let targets : List Name := ['''+', '.join('`'+n for n in heads)+''']
  let mut i : Nat := 0
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
          catch _ =>
            logInfo m!"CONTROL|{i}|{name}|{mode}|FAIL"
            logError m!"CONTROL_RFL|{i}|{name}|{mode}|rfl did not close reflected identity"
            pure none
        if mode == "abstract" then solve head info.value
        else forallTelescopeReducing info.type fun xs _ => do
          if xs.isEmpty then
            let unitTy := mkConst ``Unit
            solve (Expr.lam `_u unitTy head .default)
              (Expr.lam `_u unitTy info.value .default)
          else
            let result ← solve (mkAppN head xs) ((mkAppN info.value xs).headBeta)
            match result with
            | none => pure none
            | some (ty, value) => pure (some (← mkForallFVars xs ty, ← mkLambdaFVars xs value))
      if let some (ty, value) := result then
        let ty ← liftTermElabM <| instantiateMVars ty
        let value ← liftTermElabM <| instantiateMVars value
        if ty.hasFVar || ty.hasMVar || value.hasFVar || value.hasMVar then
          throwError "unclosed control {i}"
        let kernelName := Name.mkSimple ("ReaderRepairControl_" ++ toString i)
        liftCoreM <| addDecl (.thmDecl { name := kernelName, levelParams := info.levelParams, type := ty, value := value })
        logInfo m!"CONTROL|{i}|{name}|{mode}|PASS|kernelChecked={kernelName}"
  logInfo m!"CONTROL_COMPLETE|{i}"
''';native=top+common+body;sealed=top+common+'attribute [local irreducible] '+' '.join(heads)+'\n'+body;d=O/'controls';d.mkdir(exist_ok=True);(d/'Native.lean.txt').write_text(native);(d/'Sealed.lean.txt').write_text(sealed);(d/'SCOPE.json').write_text(json.dumps({'heads':heads,'ordinary_heads':len(heads),'paired_identities':2*len(heads),'common_smartUnfolding':False,'definition_simp_rows_removed_both':simp,'same_goals_except_seal_attribute':True,'no_transparency_override':True,'nullary_point_uses_Unit_function_lifting':True},indent=2)+'\n');print('Prepared',2*len(heads),'fresh paired reflected identities for',len(heads),'ordinary heads.')
