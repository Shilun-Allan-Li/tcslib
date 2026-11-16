import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedFields
import Lean

set_option maxErrors 0
set_option maxHeartbeats 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_of_label_ne
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_of_label_ne
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_false
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_false
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_of_ne
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.keyAt_of_ne
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.decodePair_fill
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.decodePair_fill
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.activeAnswers_fill
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.activeAnswers_fill
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_tail_stage_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_tail_stage_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_tail_fill
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_tail_fill
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.outputBit_plaintext_ne_of_lt
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.outputBit_plaintext_ne_of_lt
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.outputBit_plaintext_ne
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.outputBit_plaintext_ne
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_even
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_even
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_odd
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_odd
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_next
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stageBit_plaintext_ne_next
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_of_arity_zero
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_of_arity_zero
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_of_arity_le_one
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_of_arity_le_one
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_eq_of_stageBit_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.message_eq_of_stageBit_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.sample_eq_of_stageBit_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.sample_eq_of_stageBit_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.selectedPosition_none_bit
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.selectedPosition_none_bit
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.selectedPosition_none_getD
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.selectedPosition_none_getD
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_unselected
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_first_unselected
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_unselected
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedFields.stage_second_unselected

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! ==
          `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedFields then
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
