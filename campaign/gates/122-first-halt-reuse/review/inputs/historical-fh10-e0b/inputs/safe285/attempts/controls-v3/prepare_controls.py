from pathlib import Path
import json,shutil,hashlib
O=Path(__file__).parent;pin=json.loads((O/'PIN.json').read_text());F=json.loads((O/'FOOTPRINT-SUMMARY.json').read_text());ids={9,16,18,19,33,85,86};heads=sorted({n for r in F['rows'] if r['id'] in ids for n in r['ordinary_head_names']});assert len(heads)==11;imports=['import Lean']+['import '+p[:-5].replace('/','.') for p in sorted({r['path'] for r in pin['roots'] if r['id'] in ids})];info={r['name']:r for r in json.loads((O/'ORDINARY-UNION.json').read_text())};erase=[n for n in heads if info[n]['simp'] or info[n]['unfold']]
common='\n'.join(imports)+'\nset_option maxHeartbeats 0\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\n'
if erase:common+='attribute [-simp] '+' '.join(erase)+'\n'
body='''open Lean Elab Command Meta in
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
          catch ex =>
            logInfo m!"CONTROL|{i}|{name}|{mode}|FAIL"
            logError m!"CONTROL_RFL|{i}|{name}|{mode}|{ex.toMessageData}"
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
        let kernelName := Name.mkSimple ("FHFullControl_" ++ toString i)
        liftCoreM <| addDecl (.thmDecl { name := kernelName, levelParams := info.levelParams, type := ty, value := value })
        logInfo m!"CONTROL|{i}|{name}|{mode}|PASS|kernelChecked={kernelName}"
  logInfo m!"CONTROL_COMPLETE|{i}"
'''
rows=[]
for side in ['native','sealed']:
 P=O/'live'/('controls-'+side);(P/'.lake').mkdir(parents=True,exist_ok=True);(P/'.lake/packages').symlink_to(Path(pin['source_worktree'])/'.lake/packages',target_is_directory=True);shutil.copyfile(O/'context/lean-toolchain',P/'lean-toolchain');attr='' if side=='native' else 'attribute [local irreducible] '+' '.join(heads)+'\n';code=common+attr+body;(P/'Controls.lean').write_text(code);d=O/('Controls-'+side+'.lean.txt');d.write_text(code);rows.append({'side':side,'heads':heads,'head_count':len(heads),'identities':22,'nullary_mode':'point uses Unit-function lifting, distinct from whole-value abstract identity','project':str(P),'input':'Controls.lean','input_evidence':d.name,'input_sha256':hashlib.sha256(code.encode()).hexdigest(),'definition_simp_rows_removed_in_both':erase})
(O/'CONTROL-INPUTS.json').write_text(json.dumps(rows,indent=2)+'\n');print('Prepared22 paired controls for provisional7 union11')
