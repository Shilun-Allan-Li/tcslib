import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybrids
import Lean

set_option maxErrors 0
set_option maxHeartbeats 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_congr
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_congr
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_real
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_real
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_fake
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.rowWith_fake
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_real
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_real
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_fake
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_fake
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit_zero
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.trueBit_zero
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.values_consistent
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.values_consistent
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_relabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_start
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_start
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_end
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_end
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_even
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_even
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_odd
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_odd
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_end
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_end
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_completed
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_completed
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_future
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_future
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_zero
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_zero
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_first
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_first
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_rest
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_current_rest
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_zero
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_zero
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.assignment_zero_of_two
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.assignment_zero_of_two
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_first_unchanged
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_first_unchanged
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_other
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_other
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_unchanged
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.outputBit_second_unchanged
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_start
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.stageBit_start
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_start
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.GateHybrids.tableWith_start

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! ==
          `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybrids then
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
