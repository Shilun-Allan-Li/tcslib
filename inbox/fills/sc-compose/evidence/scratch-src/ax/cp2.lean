import TCSlib.Cryptography.SecureComputation.ComposeSecurity
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Bounds
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct

open Lean Elab Command

/-! sc-compose fill, axioms (cp2): every stored constant of the listed modules (`AX` lines) and the
targets of the brief (`ENDPOINT` lines). -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : Std.HashSet Name := Std.HashSet.ofList [`TCSlib.Cryptography.SecureComputation.ComposeSecurity, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Efficiency, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Reductions, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Assembly, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Runs, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Bounds, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Sim, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Accept, `TCSlib.Cryptography.SecureComputation.ComposeSecurity.Correct]
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
