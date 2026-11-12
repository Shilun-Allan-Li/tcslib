import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation
open Lean Elab Command

/-! Axioms of the nm-cca2 fill: the target, every stored constant of the changed and new files
(the owned file and its four helper modules, auxiliary declarations included), and
`simNMSecure_cpa_iff_nmSecure_cpa`. -/

#print axioms TCSlib.Cryptography.Composability.FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2
#print axioms TCSlib.Cryptography.Composability.FixedLengthPKScheme.simNMSecure_cpa_iff_nmSecure_cpa

def fillMods : List Name := [
  `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Readers,
  `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Forward,
  `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Decrypt,
  `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability.Encrypt,
  `TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (c, _) in env.constants.toList do
    let some i := env.getModuleIdxFor? c | continue
    let m := env.header.moduleNames[i.toNat]!
    if fillMods.contains m then
      let axs ← liftCoreM <| collectAxioms c
      let s := (axs.map toString).qsort (· < ·)
      rows := rows.push s!"{m.toString.replace "TCSlib.Cryptography.Encryption.PublicKey.NonMalleability." ""} | {c} | {s}"
  for r in rows.qsort (· < ·) do IO.println r
  IO.println s!"TOTAL {rows.size} constants"
  let bad := rows.filter fun r => !(r.endsWith "#[Classical.choice, Quot.sound, propext]" ||
    r.endsWith "#[]" || r.endsWith "#[propext]" || r.endsWith "#[Quot.sound]" ||
    r.endsWith "#[Classical.choice, propext]" || r.endsWith "#[Quot.sound, propext]" ||
    r.endsWith "#[Classical.choice]" || r.endsWith "#[Classical.choice, Quot.sound]")
  IO.println s!"OUTSIDE [propext, Classical.choice, Quot.sound]: {bad.size}"
  for r in bad do IO.println s!"  {r}"
