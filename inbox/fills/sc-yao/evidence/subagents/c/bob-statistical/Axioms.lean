import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobStatistical
import Lean

set_option maxErrors 0
set_option maxHeartbeats 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobStatistical.statClose_real_output_switch
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.BobStatistical.statClose_real_output_switch

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! ==
          `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobStatistical then
        roots := roots.push name
  logInfo m!"STORED_CONSTANT_COUNT {roots.size}"
  for root in roots do
    let axioms ← Lean.collectAxioms root
    logInfo m!"AXIOMS {root}: {axioms}"
    let mut pending := [root]
    let mut seen : NameSet := {}
    let mut found : Array Name := #[]
    let mut count := 0
    while !pending.isEmpty do
      let current := pending.head!
      pending := pending.tail
      if seen.contains current then
        continue
      seen := seen.insert current
      count := count + 1
      if let some info := env.find? current then
        if let some value := info.value? true then
          if value.hasSorry then
            found := found.push current
        pending := info.getUsedConstantsAsSet.toList ++ pending
    logInfo m!"DEPENDENCY {root}: closure={count} sorried={found}"
