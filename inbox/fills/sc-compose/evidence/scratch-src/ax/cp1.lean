import TCSlib.Cryptography.SecureComputation.ComposeSecurity
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency

open Lean Elab Command

/-! sc-compose fill, axioms (cp1): every stored constant of the listed modules (`AX` lines) and the
targets of the brief (`ENDPOINT` lines). -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : Std.HashSet Name := Std.HashSet.ofList [`TCSlib.Cryptography.SecureComputation.ComposeSecurity, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency]
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
  for e in [`TCSlib.Cryptography.SecureComputation.HybridProtocol.composeP_efficient, `TCSlib.Cryptography.SecureComputation.HybridProtocol.composeV_efficient, `TCSlib.Cryptography.SecureComputation.HybridProtocol.hbcSecure_compose, `TCSlib.Cryptography.SecureComputation.HybridProtocol.polyTime_compose] do
    if env.contains e then
      let axs ← liftCoreM <| collectAxioms e
      IO.println s!"ENDPOINT {e}: {((axs.map toString).qsort (· < ·)).toList}"
    else IO.println s!"ENDPOINT {e}: MISSING"
