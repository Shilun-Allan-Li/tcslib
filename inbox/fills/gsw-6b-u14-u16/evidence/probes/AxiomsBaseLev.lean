import lean_proof.u1416.base.LeveledBase
import Lean

/-! C5 (gsw-6b-u14-u16, base control, Leveled): `#print axioms` of the targets, then a census of every stored
constant of the listed module(s) with its axioms and, for each constant that reaches `sorryAx`, the
declarations of the import closure that use `sorryAx` directly and that it reaches (the dependency
trace). Allowed trace names (brief, Axioms): U12's `encrypts_homEvalFormula`, `encrypts_homEvalPBP`,
`Encrypts.select`; U13's `nandFormula_eval`, `depth_nandFormula_le`, `maxFanin_nandFormula_le`,
`decDepth_le`, `decryptFormula_eval`, `vecMul_secretVector_eq_sum`. Any other trace name is
counted as DISALLOWED. -/

#print axioms TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.encrypts_leveledEval
#print axioms TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.decrypt_keygen_leveledEvalCircuit

open Lean Elab Command in
/-- Glue (probe): the constants reachable from `n` (values and types) that use `sorryAx`
directly. -/
partial def u1416SorrySources (env : Environment) (n : Name) : Array Name := Id.run do
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
  let mods : List Name := [`lean_proof.u1416.base.LeveledBase]
  let std : List Name := [`propext, `Classical.choice, `Quot.sound, `sorryAx]
  let g : Name := `TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
  let allowed : List Name := [g ++ `encrypts_homEvalFormula, g ++ `encrypts_homEvalPBP,
    g ++ `Encrypts.select, g ++ `nandFormula_eval, g ++ `depth_nandFormula_le,
    g ++ `maxFanin_nandFormula_le, g ++ `decDepth_le, g ++ `decryptFormula_eval,
    g ++ `vecMul_secretVector_eq_sum]
  let mut rows : Array String := #[]
  let mut nonstd : Nat := 0
  let mut traced : Nat := 0
  let mut bad : Nat := 0
  for (n, _) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless mods.contains env.header.moduleNames[mi.toNat]! do continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    if axs.any (fun a => !std.contains a) then nonstd := nonstd + 1
    let tr := if axs.contains ``sorryAx then u1416SorrySources env n else #[]
    if !tr.isEmpty then traced := traced + 1
    let dis := tr.filter (fun t => !allowed.contains t)
    if !dis.isEmpty then bad := bad + 1
    rows := rows.push s!"{n}: axioms {axs.toList}; sorryAx trace {tr.toList}; DISALLOWED {dis.toList}"
  for r in rows.qsort (· < ·) do
    logInfo m!"CENSUS {r}"
  logInfo m!"TOTAL {rows.size} stored constants; with an axiom outside propext/Classical.choice/Quot.sound/sorryAx: {nonstd}; with a sorryAx trace: {traced}; with a DISALLOWED trace name: {bad}"
