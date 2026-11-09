from pathlib import Path
O=Path('/private/tmp/ab34-overnight-sg1-extras')
template='''
open Lean Elab Command Meta
run_cmd do
  let env ← getEnv
  let simp ← liftTermElabM getSimpTheorems
  let sourceNames : List String := ROOTS
  let mut guards : Array Name := #[]
  let mut simpDefs : Array Name := #[]
  for sourceName in sourceNames do
    let hits := env.constants.toList.filter fun (n, _) =>
      n.toString == sourceName || (isPrivateName n && n.toString.endsWith ("." ++ sourceName))
    unless hits.length == 1 do throwError "root mismatch {sourceName}: {hits.length}"
    let (root, ci) := hits.head!
    let axs ← liftCoreM <| Lean.collectAxioms root
    logInfo m!"AX|{(Json.mkObj [("root", toJson sourceName), ("kernel", toJson root.toString), ("axioms", toJson ((axs.qsort Name.lt).toList.map Name.toString))]).compress}"
    let mut pending := ci.type.getUsedConstants ++ ((ci.value?.map Expr.getUsedConstants).getD #[])
    let mut visited : Array Name := #[]
    let mut index := 0
    while index < pending.size do
      let n := pending[index]!
      index := index + 1
      if visited.contains n then continue
      visited := visited.push n
      let home := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
      let foreign := home.any fun h => (`TCSlib).isPrefixOf h
      unless foreign || home.isNone do continue
      let some info := env.find? n | continue
      match info with
      | .defnInfo d =>
        let projection := (env.getProjectionFnInfo? n).isSome
        let abbrevDecl := match d.hints with | .abbrev => true | _ => false
        let ordinary := foreign && !projection && !abbrevDecl
        let isSimp := simp.isLemma (.decl n) || simp.toUnfold.contains n
        if ordinary && !guards.contains n then guards := guards.push n
        if foreign && isSimp && !simpDefs.contains n then simpDefs := simpDefs.push n
        logInfo m!"DEF|{(Json.mkObj [("root", toJson sourceName), ("name", toJson n.toString), ("owner", toJson ((home.map Name.toString).getD "current scratch owner")), ("foreign", toJson foreign), ("projection", toJson projection), ("kernel_abbrev", toJson abbrevDecl), ("ordinary_guard", toJson ordinary), ("default_simp_definition", toJson isSimp), ("reducibility", toJson (reprStr (getReducibilityStatusCore env n)))]).compress}"
        pending := pending ++ d.type.getUsedConstants ++ d.value.getUsedConstants
      | .thmInfo _ =>
        logInfo m!"THEOREM_BOUNDARY|{(Json.mkObj [("root", toJson sourceName), ("name", toJson n.toString), ("proof_value_traversed", toJson false)]).compress}"
        pending := pending ++ info.type.getUsedConstants
      | _ => pure ()
  logInfo m!"GUARDS|{(toJson ((guards.qsort Name.lt).toList.map Name.toString)).compress}"
  logInfo m!"SIMPDEFS|{(toJson ((simpDefs.qsort Name.lt).toList.map Name.toString)).compress}"
  logInfo m!"COMPLETE|{sourceNames.length}"
'''
for key,roots in [('SafeRun',['Turing.SafeRun.zero','Turing.SafeRun.cons','Turing.SafeRun.trans']),('HardnessLeaves',['Complexity.clA5_pt_tail','Complexity.clA5_pt_head'])]:
 src=(O/(key+'-scope-native.lean.txt')).read_text()+template.replace('ROOTS',repr(roots).replace("'",'"'))
 (O/(key+'-inventory.lean.txt')).write_text(src);(O/'native-project'/(key+'Inventory.lean')).write_text(src)
print('Prepared two complete-scope reachability/AX inventories; no imported theorem values traversed.')
