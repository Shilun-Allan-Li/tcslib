import TCSlib.Cryptography.SecureComputation.YaoReal
import Lean

set_option maxErrors 0

#print axioms TCSlib.Cryptography.SecureComputation.yaoHybrid_polyTime
#print axioms TCSlib.Cryptography.SecureComputation.yaoHybrid_simulators
#print axioms TCSlib.Cryptography.SecureComputation.yaoHybrid_hbcSecure
#print axioms TCSlib.Cryptography.SecureComputation.yaoProtocol_hbcSecure

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    `TCSlib.Cryptography.SecureComputation.yaoHybrid_polyTime,
    `TCSlib.Cryptography.SecureComputation.yaoHybrid_simulators,
    `TCSlib.Cryptography.SecureComputation.yaoHybrid_hbcSecure,
    `TCSlib.Cryptography.SecureComputation.yaoProtocol_hbcSecure]
  for root in roots do
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
