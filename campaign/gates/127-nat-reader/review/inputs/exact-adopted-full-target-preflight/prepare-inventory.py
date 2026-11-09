from pathlib import Path
O=Path('/private/tmp/ab34-nat-reader-closure-refinement');P=O/'project';s=(O/'owner-proposed.lean.txt').read_text();lines=s.splitlines(True);last=max(i for i,l in enumerate(lines) if l.startswith('import '));lines.insert(last+1,'import Lean\n');s=''.join(lines)
meta=r'''
open Lean Elab Command Meta
run_cmd do
  let env ← getEnv
  let simp ← liftTermElabM getSimpTheorems
  let sourceName := "Turing.MachineFormat.canonOffset_spec"
  let hits := env.constants.toList.filter fun (n, _) =>
    (n.toString == sourceName || (isPrivateName n && n.toString.endsWith ("." ++ sourceName))) &&
    (env.getModuleIdxFor? n).isNone
  unless hits.length == 1 do throwError "root mismatch {sourceName}: {hits.length}"
  let (root, ci) := hits.head!
  let axs ← liftCoreM <| Lean.collectAxioms root
  logInfo m!"AX|{(Json.mkObj [("root", toJson sourceName), ("kernel", toJson root.toString), ("axioms", toJson ((axs.qsort Name.lt).toList.map Name.toString)), ("full_type_Expr_repr", toJson (reprStr ci.type)), ("universes", toJson (ci.levelParams.map Name.toString)), ("private", toJson (isPrivateName root)), ("simp_lemma", toJson (simp.isLemma (.decl root))), ("simp_unfold", toJson (simp.toUnfold.contains root))]).compress}"
  let mut pending := ci.type.getUsedConstants ++ ((ci.value?.map Expr.getUsedConstants).getD #[])
  let mut visited : Array Name := #[]
  let mut guards : Array Name := #[]
  let mut simpDefs : Array Name := #[]
  let mut index := 0
  while index < pending.size do
    let n := pending[index]!
    index := index + 1
    if visited.contains n then continue
    visited := visited.push n
    let home := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!
    let own := home.isNone
    let foreignTCS := home.any fun m => (`TCSlib).isPrefixOf m
    let focusedMathlib := n == ``Nat.bit
    unless own || foreignTCS || focusedMathlib do continue
    let some info := env.find? n | continue
    match info with
    | .defnInfo d =>
      let projection := (env.getProjectionFnInfo? n).isSome
      let abbrevDecl := match d.hints with | .abbrev => true | _ => false
      let ordinary := (foreignTCS || focusedMathlib) && !projection && !abbrevDecl
      let isSimp := simp.isLemma (.decl n) || simp.toUnfold.contains n
      if ordinary && !guards.contains n then guards := guards.push n
      if ordinary && isSimp && !simpDefs.contains n then simpDefs := simpDefs.push n
      logInfo m!"DEF|{(Json.mkObj [("name", toJson n.toString), ("owner", toJson ((home.map Name.toString).getD "current CodeSimulator owner")), ("own", toJson own), ("foreign_TCS", toJson foreignTCS), ("focused_Mathlib", toJson focusedMathlib), ("projection", toJson projection), ("kernel_abbrev", toJson abbrevDecl), ("ordinary_guard", toJson ordinary), ("default_simp_definition", toJson isSimp)]).compress}"
      pending := pending ++ d.type.getUsedConstants ++ d.value.getUsedConstants
    | .thmInfo _ =>
      logInfo m!"THEOREM_BOUNDARY|{(Json.mkObj [("name", toJson n.toString), ("owner", toJson ((home.map Name.toString).getD "current CodeSimulator owner")), ("proof_value_traversed", toJson own)]).compress}"
      pending := pending ++ info.type.getUsedConstants
      if own then pending := pending ++ ((info.value?.map Expr.getUsedConstants).getD #[])
    | _ => pure ()
  logInfo m!"GUARDS|{(toJson ((guards.qsort Name.lt).toList.map Name.toString)).compress}"
  logInfo m!"SIMPDEFS|{(toJson ((simpDefs.qsort Name.lt).toList.map Name.toString)).compress}"
  logInfo m!"COMPLETE|1"
'''
(O/'OwnerInventory.lean.txt').write_text(s+meta);(P/'OwnerInventory.lean').write_text(s+meta);print('Prepared full-owner inventory: root+same-owner theorem/definition types and values; imported theorem proof boundaries; ordinary imported TCS defs plus Nat.bit.')
