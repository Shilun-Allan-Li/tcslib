from pathlib import Path
import json,shutil,hashlib
O=Path(__file__).parent;pin=json.loads((O/'PIN.json').read_text());roots=json.loads(Path('/private/tmp/ab34-first-halt-full-boundary/EXPORT-REPAIRS3/SELECTED-ROOT-TYPES10.json').read_text());P=O/'live/BASE-selected';(P/'.lake').mkdir(parents=True);W=Path(pin['source_worktree']);(P/'.lake/packages').symlink_to(W/'.lake/packages',target_is_directory=True);shutil.copyfile(W/'lean-toolchain',P/'lean-toolchain');code='\n'.join(['import Lean']+['import '+r['path'][:-5].replace('/','.') for r in pin['owners']])+'\nset_option maxHeartbeats 0\nopen Lean Elab Command Meta in\nrun_cmd do\n  let env ← getEnv\n  let targets : List String := '+json.dumps([r['root'] for r in roots],ensure_ascii=False)+'''\n  for s in targets do
    let selectedMatches := env.constants.toList.filter fun (n, _) => n.toString == s
    unless selectedMatches.length == 1 do throwError "target selectedMatches {s}: {selectedMatches.length}"
    let (n, ci) := selectedMatches.head!
    let some moduleIdx := env.getModuleIdxFor? n | throwError "not imported {n}"
    let home := env.header.moduleNames[moduleIdx.toNat]!
    let axs ← liftCoreM <| Lean.collectAxioms n
    let ty ← liftTermElabM <| ppExpr ci.type
    let kind := match ci with | .thmInfo _ => "theorem" | _ => "other"
    logInfo m!"SELECTED|{(Json.mkObj [("root",toJson n.toString),("owner",toJson home.toString),("kind",toJson kind),("type_Expr",toJson (reprStr ci.type)),("type_pretty",toJson ty.pretty),("universe_params",toJson (ci.levelParams.map Name.toString)),("axioms",toJson ((axs.qsort Name.lt).toList.map Name.toString))]).compress}"
  logInfo m!"SELECTED_COMPLETE|{targets.length}"
''';(P/'BaseSelected.lean').write_text(code);(O/'BASE-selected.lean.txt').write_text(code);(O/'BASE-SELECTED-INPUT.json').write_text(json.dumps({'project':str(P),'input':'BaseSelected.lean','input_sha256':hashlib.sha256(code.encode()).hexdigest(),'BASE':pin['BASE'],'whole_MAC8895_binding':'BINDING-CHECK.json in safe7 and repair packets','scope':'Selected10 exact imported root types/universes/kind/AX from actual wholeMAC8. Imported theorem values traversed by collectAxioms only for AX census, never definition footprint.'},indent=2)+'\n')
