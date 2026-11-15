import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM

open Lean Elab Command

/-! prf-long fill, axioms (cp2): every stored constant of the listed modules (`AX` lines) and the
consumer endpoints of the brief (`ENDPOINT` lines). -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : Std.HashSet Name := Std.HashSet.ofList [`TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs, `TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.Hybrid, `TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine]
  let mut out : Array String := #[]
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mods.contains mod do continue
    let axs ← liftCoreM <| collectAxioms c
    let axs := (axs.map toString).qsort (· < ·)
    out := out.push s!"AX\t{mod}\t{c}\t{axs.toList}"
  for s in out.qsort (· < ·) do IO.println s
  IO.println s!"TOTAL {out.size}"
  for e in [`TCSlib.Cryptography.prfScheme_multiMessageSecure, `TCSlib.Cryptography.exists_multiMessageSecure_of_exists_prg, `TCSlib.Cryptography.Composability.prfFixedScheme_cpa, `TCSlib.Cryptography.Composability.ccaScheme_cca2, `TCSlib.Cryptography.exists_prf_of_exists_prg] do
    if env.contains e then
      let axs ← liftCoreM <| collectAxioms e
      IO.println s!"ENDPOINT {e}: {((axs.map toString).qsort (· < ·)).toList}"
    else IO.println s!"ENDPOINT {e}: MISSING"
