import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag

/-! Axioms of the target and of every stored constant of the changed and new modules of the fill
`cca2-ett` (one row per constant: module, constant, axioms), with a summary. -/

open Lean Elab Command

#print axioms TCSlib.Cryptography.Composability.ccaScheme_cca2

run_cmd do
  let env ← getEnv
  let pre := `TCSlib.Cryptography.Encryption.PrivateKey
  let mods : List Name := [pre ++ `EncryptThenTag,
    pre ++ `EncryptThenTag.Tools, pre ++ `EncryptThenTag.Machines, pre ++ `EncryptThenTag.Games,
    pre ++ `EncryptThenTag.Handler, pre ++ `EncryptThenTag.Reduction,
    pre ++ `EncryptThenTag.Transfer, pre ++ `EncryptThenTag.Forgery, pre ++ `EncryptThenTag.Lazy,
    pre ++ `EncryptThenTag.CPAHandler, pre ++ `EncryptThenTag.CPAReduction]
  let mut rows : Array String := #[]
  let mut all : Array Name := #[]
  let mut perMod : Std.HashMap Name Nat := {}
  for (n, _) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless mods.contains m do continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless all.contains a do all := all.push a
    perMod := perMod.insert m (perMod.getD m 0 + 1)
    rows := rows.push s!"{m}\t{n}\t{axs.toList}"
  let sorted := rows.qsort (· < ·)
  for r in sorted do
    IO.println r
  for m in mods do
    IO.println s!"MODULE {m}: {perMod.getD m 0} stored constants"
  IO.println s!"TOTAL {sorted.size} stored constants; axioms used (union): {(all.qsort (fun a b => a.toString < b.toString)).toList}"
