import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SamplerEndpoints
import Lean

set_option maxErrors 0
set_option maxHeartbeats 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.real_eq_stage0_on_tape
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.real_eq_stage0_on_tape
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_real_eq_stage0
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_real_eq_stage0
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_real_eq_stage0_fst
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_real_eq_stage0_fst
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.distAdv_real_stage0_zero
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.distAdv_real_stage0_zero
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.sample_end_of_result
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.sample_end_of_result
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_end_eq_fake
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_end_eq_fake
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_end_eq_ideal
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.acceptProb_end_eq_ideal
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.distAdv_end_ideal_zero
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SamplerEndpoints.distAdv_end_ideal_zero

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! ==
          `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SamplerEndpoints then
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
