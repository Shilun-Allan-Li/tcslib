import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinRelabel
import Lean

set_option maxErrors 0
set_option maxHeartbeats 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.Blocks_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_key
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_key
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_row
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_row
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_shift
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_shift
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.splitTape_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_key
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_key
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_row
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_row
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_shift
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_shift
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blocksEquiv_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.keyRelabel_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.rowRelabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.rowRelabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.rowRelabel_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.rowRelabel_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.shiftRelabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.shiftRelabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.shiftRelabel_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.shiftRelabel_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blockRelabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blockRelabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blockRelabel_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.blockRelabel_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_blocks
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_blocks
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key_getD
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key_getD
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row_getD
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row_getD
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift_getD
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift_getD
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key_fixed
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_key_fixed
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row_fixed
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_row_fixed
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift_fixed
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.CoinRelabel.relabel_shift_fixed

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! ==
          `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinRelabel then
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
