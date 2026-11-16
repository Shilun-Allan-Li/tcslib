import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RelabelGarbling
import Lean

set_option maxErrors 0
set_option maxHeartbeats 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues_apply
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argValues_apply
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_key
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_key
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_coin
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_coin
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_perm
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.relabelSeed_perm
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.keyAt_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.keyAt_relabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.keyAt_original
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.keyAt_original
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argKeys_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.argKeys_relabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.row_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.row_relabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.garbledTable_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.garbledTable_relabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.inputKeys_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.inputKeys_relabel
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.selectedKeys_original
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.selectedKeys_original
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.output_pair_relabel
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.RelabelGarbling.output_pair_relabel

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! ==
          `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RelabelGarbling then
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
