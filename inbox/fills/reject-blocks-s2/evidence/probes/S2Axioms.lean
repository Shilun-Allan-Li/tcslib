import TCSlib.Cryptography.Candidates

/-! S2 axiom log: H15's axioms, then every declaration of the five owned modules (private and
generated ones included) with its axioms, as `AXIOMS <module> <decl> <axioms>` lines. -/

#print axioms TCSlib.Cryptography.Candidates.polyTimeComputable_rejectBlocksL

open Lean Elab Command in
elab "#s2_axiom_walk" : command => do
  let env ← getEnv
  let mods := [`TCSlib.Cryptography.Candidates.Concrete, `TCSlib.Cryptography.Candidates.DiscreteLog,
    `TCSlib.Cryptography.Candidates.ElGamal, `TCSlib.Cryptography.Candidates.RSA,
    `TCSlib.Cryptography.Candidates.Rabin]
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mods.contains mod do continue
    -- theorems and definitions only (skip recursors/constructors/matchers' auxiliaries noise)
    match ci with
    | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
      let axs ← liftCoreM <| Lean.collectAxioms n
      lines := lines.push s!"AXIOMS\t{mod}\t{n}\t{(axs.qsort Name.lt).toList}"
    | _ => pure ()
  logInfo (String.intercalate "\n" (lines.qsort (· < ·)).toList)

#s2_axiom_walk
