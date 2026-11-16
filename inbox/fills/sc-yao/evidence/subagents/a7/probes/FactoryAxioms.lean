import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.ChunkScanner
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinGarbling
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.WordLists
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RowFromCoins
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TablesFromCoins
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AllTables
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GarblingProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AliceProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeObjects
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeMessage
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulator
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoordinateSwap
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobViewShape
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulatorFactory
import evidence.subagents.a7.probes.ConcreteFactory
import Lean

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Lean Elab Command

partial def scYaoA7FactoryClosure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
    if seen.contains name then scYaoA7FactoryClosure env rest seen else
      let deps := match env.find? name with
        | none => []
        | some ci => ci.getUsedConstantsAsSet.toList
      scYaoA7FactoryClosure env (deps ++ rest) (seen.insert name)

run_cmd do
  let env ← getEnv
  let modules := #[
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.ChunkScanner,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoinGarbling,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.WordLists,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.RowFromCoins,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.TablesFromCoins,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AllTables,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GarblingProgram,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AliceProgram,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeObjects,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeProgram,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeMessage,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulator,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.CoordinateSwap,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobViewShape,
    `TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulatorFactory,
    `evidence.subagents.a7.probes.ConcreteFactory]
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[idx.toNat]! then
        count := count + 1
        logInfo m!"SIGNATURE\t{name}\t{ci.type}"
        let axioms ← collectAxioms name
        logInfo m!"AXIOMS\t{name}\t{axioms.qsort Name.lt}"
        let closure := scYaoA7FactoryClosure env [name] {}
        let mut sorried : Array Name := #[]
        for dependency in closure.toList do
          if let some dependencyInfo := env.find? dependency then
            if dependencyInfo.getUsedConstantsAsSet.contains ``sorryAx then
              sorried := sorried.push dependency
        logInfo m!"SORRY_CLOSURE\t{name}\t{sorried.qsort Name.lt}"
  logInfo m!"STORED_CONSTANTS {count}"
