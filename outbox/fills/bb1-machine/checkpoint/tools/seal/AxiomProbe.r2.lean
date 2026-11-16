import TCSlib.Cryptography.Pairing
import TCSlib.Cryptography.KeyExchange
import TCSlib.Cryptography.AdvancedEncryption
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : List Name := [`TCSlib.Cryptography.Pairing.Group, `TCSlib.Cryptography.Pairing.Assumptions,
    `TCSlib.Cryptography.Pairing.Operations, `TCSlib.Cryptography.KeyExchange.Joux,
    `TCSlib.Cryptography.AdvancedEncryption.IdentityBased.Defs, `TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen,
    `TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine,
    `TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity, `TCSlib.Cryptography.Pairing,
    `TCSlib.Cryptography.KeyExchange, `TCSlib.Cryptography.AdvancedEncryption.IdentityBased, `TCSlib.Cryptography.AdvancedEncryption]
  let idxs := mods.filterMap env.getModuleIdx?
  let mut out : Array String := #[]
  for (n, _) in env.constants.toList do
    match env.getModuleIdxFor? n with
    | some i =>
      if idxs.contains i then
        let axs ← liftCoreM (Lean.collectAxioms n)
        let tag := if n.isInternal then "AUX" else "DECL"
        out := out.push s!"{tag}\t{n}\t{axs.qsort (·.toString < ·.toString) |>.toList}"
    | none => pure ()
  for l in out.qsort (· < ·) do
    IO.println l
