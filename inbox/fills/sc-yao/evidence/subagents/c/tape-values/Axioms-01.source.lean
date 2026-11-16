import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues
import Lean

set_option maxErrors 0
set_option maxHeartbeats 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.keyEmbedding_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.rowEmbedding_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.Rest_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_shift
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_shift
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_key
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_key
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_nonce_first
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_nonce_first
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_nonce_second
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_nonce_second
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_unused_key
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_unused_key
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_unused_row
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.equiv_unused_row
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation_apply
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.permutation_apply
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_perm
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_perm
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_on_inverse
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.seed_on_inverse
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.key_not_mem_range
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.key_not_mem_range
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_gate
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_gate
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_code
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.TapeValues.row_not_mem_range_of_code

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! ==
          `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TapeValues then
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
