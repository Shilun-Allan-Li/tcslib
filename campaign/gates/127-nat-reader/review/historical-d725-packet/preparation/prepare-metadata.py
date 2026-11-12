from pathlib import Path
import json
O=Path('/private/tmp/ab34-small-gate-drafts');P=O/'metadata-project';sc=json.loads((O/'scope.json').read_text())
body='''
open Lean Elab Command Meta
run_cmd do
  let env ← getEnv
  let simp ← liftTermElabM getSimpTheorems
  let owner := OWNER
  let roots : List String := ROOTS
  for sourceName in roots do
    let hits := env.constants.toList.filter fun (n, _) =>
      (n.toString == sourceName || (isPrivateName n && n.toString.endsWith ("." ++ sourceName))) &&
      ((env.getModuleIdxFor? n).any fun i => env.header.moduleNames[i.toNat]!.toString == owner)
    unless hits.length == 1 do throwError "selected root mismatch {sourceName}: {hits.length}"
    let (n, ci) := hits.head!
    let axs ← liftCoreM <| Lean.collectAxioms n
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "definition"
      | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque" | _ => "other"
    let used := ci.type.getUsedConstants.qsort Name.lt
    logInfo m!"ABI|{(Json.mkObj [("source_name", toJson sourceName), ("kernel_name", toJson n.toString), ("owner", toJson owner), ("private", toJson (isPrivateName n)), ("kind", toJson kind), ("universe_parameters", toJson (ci.levelParams.map Name.toString)), ("full_type_Expr_repr", toJson (reprStr ci.type)), ("type_Expr_without_mdata_repr", toJson (reprStr ci.type.consumeMData)), ("type_constants", toJson (used.toList.map Name.toString)), ("simp_lemma", toJson (simp.isLemma (.decl n))), ("simp_unfold", toJson (simp.toUnfold.contains n)), ("axioms", toJson ((axs.qsort Name.lt).toList.map Name.toString))]).compress}"
    for dep in used do
      if !isPrivateName dep then continue
      let some info := env.find? dep | continue
      let prop ← liftTermElabM <| isProp info.type
      let home := (env.getModuleIdxFor? dep).map fun i => env.header.moduleNames[i.toNat]!.toString
      logInfo m!"TYPE_AUX|{(Json.mkObj [("root", toJson sourceName), ("name", toJson dep.toString), ("owner", toJson home), ("type_is_Prop", toJson prop), ("universes", toJson (info.levelParams.map Name.toString)), ("full_type_Expr_repr", toJson (reprStr info.type))]).compress}"
  logInfo m!"COMPLETE|{roots.length}"
'''
for item in sc['items']:
 module=item['owner'][:-5].replace('/','.');src='import '+module+'\nimport Lean\nset_option maxHeartbeats 0\n'+body.replace('OWNER',json.dumps(module)).replace('ROOTS',json.dumps(item['roots']))
 label='Gate'+str(item['gate'])+'SelectedMetadata.lean';(P/label).write_text(src);(O/str(item['gate'])/'selected-metadata-probe.lean.txt').write_text(src)
print('Prepared compact selected-root ABI/fulltype/universe/simp/AX probes; no pp.width and no theorem proof values dumped.')
