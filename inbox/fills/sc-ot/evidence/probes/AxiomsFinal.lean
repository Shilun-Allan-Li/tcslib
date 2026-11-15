import TCSlib.Cryptography.SecureComputation.ObliviousTransfer
import Lean

/-! Axioms of the two targets, and of every stored constant of the changed and new modules
(the owned module and the six helpers), enumerated from the environment. -/

#print axioms TCSlib.Cryptography.SecureComputation.otProtocol_polyTime
#print axioms TCSlib.Cryptography.SecureComputation.otProtocol_simulators
#print axioms TCSlib.Cryptography.SecureComputation.otProtocol_hbcSecure

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mods : List Name := [`TCSlib.Cryptography.SecureComputation.ObliviousTransfer,
    `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Shape,
    `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Efficiency,
    `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Simulators,
    `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewA,
    `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.Predictor,
    `TCSlib.Cryptography.SecureComputation.ObliviousTransfer.ViewB]
  let std : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array (String × String) := #[]
  let mut nonstd : Nat := 0
  for (n, _) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless mods.contains m do continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    if axs.any (fun a => !std.contains a) then nonstd := nonstd + 1
    rows := rows.push (s!"{m}", s!"{n}: {axs.toList}")
  let sorted := rows.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2))
  for (m, r) in sorted do
    logInfo m!"AXIOMS {m} {r}"
  logInfo m!"TOTAL {sorted.size} stored constants; with a non-standard axiom: {nonstd}"
