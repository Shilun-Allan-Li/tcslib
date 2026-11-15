import TCSlib.Cryptography.Authentication.MAC.FromPRF.Handler
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction
import TCSlib.Cryptography.Authentication.MAC.FromPRF.Random
import TCSlib.Cryptography.Authentication.MAC.FromPRF

open Lean Elab Command

/-! prf-mac fill, axioms (cp2): every stored constant of the listed modules, one `AX` line each,
and the target `prfMAC_secure` (`TARGET` line). -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : Std.HashSet Name := Std.HashSet.ofList [`TCSlib.Cryptography.Authentication.MAC.FromPRF.Handler, `TCSlib.Cryptography.Authentication.MAC.FromPRF.Reduction, `TCSlib.Cryptography.Authentication.MAC.FromPRF.Random, `TCSlib.Cryptography.Authentication.MAC.FromPRF]
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
  let t := `TCSlib.Cryptography.Authentication.prfMAC_secure
  if env.contains t then
    let axs ← liftCoreM <| collectAxioms t
    IO.println s!"TARGET {t}: {((axs.map toString).qsort (· < ·)).toList}"
