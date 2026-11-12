import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Axioms of every stored constant of the changed and new files of the nm-sim fill (the owned
file and the ten helper modules), private and auxiliary constants included. -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := #["TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation",
    "TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Generic",
    "TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Hybrid",
    "TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimIND",
    "TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.SimINDGap",
    "TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Rounds",
    "TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Challenge",
    "TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Simulator",
    "TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Reduction",
    "TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.Recover",
    "TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation.IndSim"]
  let mut total := 0
  let mut bad := 0
  let mut lines : Array String := #[]
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!.toString
    unless mods.contains mod do continue
    let axs ← liftCoreM <| collectAxioms c
    let axs := axs.qsort (fun a b => a.toString < b.toString)
    total := total + 1
    let ok := axs.all fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound
    unless ok do bad := bad + 1
    lines := lines.push s!"{mod.drop 57} {c} {axs.toList}"
  for l in lines.qsort (· < ·) do IO.println l
  IO.println s!"TOTAL {total} constants; {bad} with axioms outside propext, Classical.choice, Quot.sound"
