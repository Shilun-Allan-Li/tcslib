import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridMessage
import Lean

set_option maxErrors 0
set_option maxHeartbeats 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.activeAnswers_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.activeAnswers_relabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.decodePair_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.decodePair_relabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_relabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_end
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.message_end
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_relabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_end
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybridMessage.sample_end

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! ==
          `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybridMessage then
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
