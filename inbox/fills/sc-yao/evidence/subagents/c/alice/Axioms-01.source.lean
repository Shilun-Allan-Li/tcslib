import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AliceSimulator
import Lean

set_option maxErrors 0

#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.polyTimeComputable_raw
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.polyTimeComputable_raw
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_eq
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_eq
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_uniform
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_uniform
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_coins
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_coins
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_runAtL
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_runAtL
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.statClose_real_ideal
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.statClose_real_ideal
#check TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.distAdv_real_ideal_le
#print axioms TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.distAdv_real_ideal_le

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.raw_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.polyTimeComputable_raw,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_eq,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_uniform,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_coins,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.simulator_runAtL,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.statClose_real_ideal,
    `TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceSimulator.distAdv_real_ideal_le]
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
