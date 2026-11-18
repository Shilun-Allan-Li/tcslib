import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula
import Lean

/-! C5 (gsw-6b-u13): `#print axioms` of the six targets, then a census of every stored constant
of the owned module with its axioms and, for each constant that reaches `sorryAx`, the
declarations of the import closure that use `sorryAx` directly and that it reaches (the
dependency trace; expected empty). -/

#print axioms TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.vecMul_secretVector_eq_sum
#print axioms TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decryptFormula_eval
#print axioms TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.nandFormula_eval
#print axioms TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.depth_nandFormula_le
#print axioms TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.maxFanin_nandFormula_le
#print axioms TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decDepth_le

open Lean Elab Command in
/-- Glue (probe): the constants reachable from `n` (values and types) that use `sorryAx`
directly. -/
partial def u13SorrySources (env : Environment) (n : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[n]
  let mut out : Array Name := #[]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let consts := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
    if consts.contains ``sorryAx then out := out.push c
    for d in consts do
      unless seen.contains d do stack := stack.push d
  return out

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods : List Name := [`TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula]
  let std : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array String := #[]
  let mut nonstd : Nat := 0
  let mut traced : Nat := 0
  for (n, _) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless mods.contains env.header.moduleNames[mi.toNat]! do continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    if axs.any (fun a => !std.contains a) then nonstd := nonstd + 1
    let tr := if axs.contains ``sorryAx then u13SorrySources env n else #[]
    if !tr.isEmpty then traced := traced + 1
    rows := rows.push s!"{n}: axioms {axs.toList}; sorryAx trace {tr.toList}"
  for r in rows.qsort (· < ·) do
    logInfo m!"CENSUS {r}"
  logInfo m!"TOTAL {rows.size} stored constants of the owned module; with a non-standard axiom: {nonstd}; with a sorryAx trace: {traced}"
