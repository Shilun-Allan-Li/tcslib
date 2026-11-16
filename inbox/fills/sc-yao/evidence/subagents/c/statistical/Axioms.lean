import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.StatisticalSwitch
import Lean

set_option maxErrors 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch.statClose_of_eq_off
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch.statClose_of_eq_off
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch.distAdv_le_of_eq_off
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch.distAdv_le_of_eq_off

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch.statClose_of_eq_off,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.StatisticalSwitch.distAdv_le_of_eq_off]
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
