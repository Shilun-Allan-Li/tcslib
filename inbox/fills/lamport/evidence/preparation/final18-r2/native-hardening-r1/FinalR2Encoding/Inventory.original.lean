import Lean
import LamportEvidence.Seals.FinalR2Encoding.Snapshot0

set_option maxHeartbeats 0
open Lean Meta Elab Command

run_cmd do
  let target : String := "TCSlib.Cryptography.Authentication.Signatures.Lamport.Encoding"
  let ownHome : String := "LamportEvidence.Seals.FinalR2Encoding.Snapshot0"
  let payload : String := "TCSlib.Complexity.ClassNP.CounterProgPolyTime\nTCSlib.Complexity.ClassNP.PolyTime\nTCSlib.Complexity.ClassNP.PolyTimeBlockLoop\nTCSlib.Complexity.ClassNP.PolyTimePairing\nTCSlib.Complexity.ClassNP.PolyTimePrefix\nTCSlib.Complexity.ClassNP.Transducer\nTCSlib.Complexity.ClassP.BinaryArith.Basic\nTCSlib.Complexity.ClassP.BinaryArith.Iterate\nTCSlib.Complexity.ClassP.TimeConstructible\nTCSlib.Complexity.Randomized.Build.IterateFind\nTCSlib.Complexity.Randomized.Build.IterateFindHost\nTCSlib.Complexity.Randomized.Build.PairSplit\nTCSlib.Complexity.Randomized.Build.StateLoop\nTCSlib.Complexity.Randomized.Build.StringLoops\nTCSlib.Complexity.Randomized.Build.UnaryMul\nTCSlib.Complexity.Randomized.Closure\nTCSlib.Complexity.Randomized.PPT\nTCSlib.Complexity.Randomized.PolyExpr\nTCSlib.Complexity.Randomized.Primitives\nTCSlib.Complexity.Randomized.Repetition\nTCSlib.Complexity.SpaceComplexity.Machines.Bin\nTCSlib.Complexity.TuringMachine.Build.Convention\nTCSlib.Complexity.TuringMachine.Build.Embed\nTCSlib.Complexity.TuringMachine.Build.EmitIterBody\nTCSlib.Complexity.TuringMachine.Build.EmitIterEmbed\nTCSlib.Complexity.TuringMachine.Build.Loop\nTCSlib.Complexity.TuringMachine.Build.ModuleHost\nTCSlib.Complexity.TuringMachine.Build.Primitives\nTCSlib.Complexity.TuringMachine.Build.Wrappers\nTCSlib.Complexity.TuringMachine.Composition\nTCSlib.Complexity.TuringMachine.Configuration\nTCSlib.Complexity.TuringMachine.CounterProg\nTCSlib.Complexity.TuringMachine.CounterProgInput\nTCSlib.Complexity.TuringMachine.CounterProgRun\nTCSlib.Complexity.TuringMachine.Deterministic\nTCSlib.Complexity.TuringMachine.Encoding\nTCSlib.Complexity.TuringMachine.Finite\nTCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction\nTCSlib.Complexity.TuringMachine.Robustness.SingleTape\nTCSlib.Complexity.TuringMachine.Simulation\nTCSlib.Complexity.TuringMachine.StateRenaming\nTCSlib.Complexity.TuringMachine.Sweep\nTCSlib.Complexity.TuringMachine.UnaryTape\nTCSlib.Cryptography.Asymptotic.Adversary\nTCSlib.Cryptography.Encryption.PrivateKey.EnsembleSecurity\nTCSlib.Cryptography.Encryption.PrivateKey.Scheme\nTCSlib.Cryptography.Foundations.BitLists\nTCSlib.Cryptography.Foundations.Experiments\nTCSlib.Cryptography.Foundations.Negligible\nTCSlib.Cryptography.Foundations.Probability\nTCSlib.Cryptography.HardcoreBit.Basic\nTCSlib.InformationTheory.FinDist\nTCSlib.InformationTheory.StatisticalDistance"
  let homes := if payload.isEmpty then [] else payload.splitOn "\n"
  let env ← getEnv
  unless env.header.moduleNames.any (fun m => m.toString == ownHome) do
    throwError "LAMP-INVENTORY missing own snapshot {ownHome}"
  for home in homes do
    unless env.header.moduleNames.any (fun m => m.toString == home) do
      throwError "LAMP-INVENTORY missing closure module {home}"
  let mut rows : Array String := #[]
  let mut axs : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[mi.toNat]!.toString
    unless home == ownHome || homes.contains home do continue
    let status ← liftCoreM <| getReducibilityStatus n
    let matcher := (Match.Extension.getMatcherInfo? env n).isSome
    let instanceFlag := isInstanceCore env n
    rows := rows.push s!"LAMP-CATALOG\t{target}\t{n.toString}\t{home}\t{ci.isDefinition}\t{instanceFlag}\t{matcher}\t{repr status}"
    if home == ownHome then
      let aa ← liftCoreM <| collectAxioms n
      let aa := aa.qsort (fun a b => a.toString < b.toString)
      axs := axs.push s!"LAMP-AXIOMS\t{target}\t{n.toString}\t{aa.toList}"
  for row in rows.qsort (· < ·) do logInfo m!"{row}"
  for row in axs.qsort (· < ·) do logInfo m!"{row}"
  logInfo m!"LAMP-INVENTORY-END\t{target}\t{rows.size}\t{axs.size}\t{homes.length}"

