import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinSeedRelabel
import Lean

set_option maxErrors 0
set_option maxHeartbeats 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_four
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_four
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_pow
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_lt_pow
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentFold_injective
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding_lt_pow
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentEmbedding_lt_pow
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_code
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_code
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_unused
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.assignmentPerm_unused
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_vertex
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_vertex
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_gate
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_gate
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_fold
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_fold
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_argument
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_argument
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_unused
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.keyMask_unused
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_unused_gate
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_unused_gate
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_unused_code
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.rowPerm_unused_code
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_unused_gate
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_unused_gate
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_unused_argument
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.shiftMask_unused_argument
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_key_getD
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_key_getD
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_row_getD
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_row_getD
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_shift_getD
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.relabel_shift_getD
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.seed_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinSeedRelabel.seed_relabel

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! ==
          `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinSeedRelabel then
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
