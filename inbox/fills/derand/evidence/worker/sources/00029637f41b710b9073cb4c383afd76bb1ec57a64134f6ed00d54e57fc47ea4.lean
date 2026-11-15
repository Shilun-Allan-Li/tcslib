import Lean
import TCSlib.Complexity.ClassP.DTIME
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.Randomized.Build.IterateFind
import TCSlib.Complexity.Randomized.SeedMajority
import TCSlib.Cryptography.Randomness.Derandomization
import TCSlib.Cryptography.Randomness.Derandomization.RootSchedule
import TCSlib.Cryptography.Randomness.Derandomization.AdviceGap
import TCSlib.Cryptography.Randomness.Derandomization.Expanded
import TCSlib.Cryptography.Randomness.Derandomization.CoinGap
import TCSlib.Cryptography.Randomness.Derandomization.Majority
import TCSlib.Cryptography.Randomness.Derandomization.TimeBound
import TCSlib.Complexity.Randomized.SeedMajority.Words
import TCSlib.Complexity.Randomized.SeedMajority.State
import TCSlib.Complexity.Randomized.SeedMajority.Enumeration
import TCSlib.Complexity.Randomized.SeedMajority.Envelope
import TCSlib.Complexity.Randomized.Repetition

set_option maxHeartbeats 0
set_option maxRecDepth 65536

run_cmd do
  let env ← Lean.getEnv
  let modules : List String := ["TCSlib.Complexity.ClassP.DTIME", "TCSlib.Complexity.Randomized.Classes", "TCSlib.Complexity.Randomized.Build.IterateFind", "TCSlib.Complexity.Randomized.SeedMajority", "TCSlib.Cryptography.Randomness.Derandomization", "TCSlib.Cryptography.Randomness.Derandomization.RootSchedule", "TCSlib.Cryptography.Randomness.Derandomization.AdviceGap", "TCSlib.Cryptography.Randomness.Derandomization.Expanded", "TCSlib.Cryptography.Randomness.Derandomization.CoinGap", "TCSlib.Cryptography.Randomness.Derandomization.Majority", "TCSlib.Cryptography.Randomness.Derandomization.TimeBound", "TCSlib.Complexity.Randomized.SeedMajority.Words", "TCSlib.Complexity.Randomized.SeedMajority.State", "TCSlib.Complexity.Randomized.SeedMajority.Enumeration", "TCSlib.Complexity.Randomized.SeedMajority.Envelope"]
  let mut count : Nat := 0
  for (name, ci) in env.constants.toList.toArray.qsort (fun a b => Lean.Name.lt a.1 b.1) do
    let some idx := env.getModuleIdxFor? name | continue
    let home := env.header.moduleNames[idx.toNat]!
    unless modules.contains home.toString ||
      name == `Complexity.polyTimeComputable_iterateFind do continue
    let axioms ← Lean.collectAxioms name
    let printed ← Lean.Elab.Command.liftTermElabM <| Lean.PrettyPrinter.ppExpr ci.type
    let row := Lean.Json.mkObj [
      ("name", Lean.toJson name.toString), ("home", Lean.toJson home.toString),
      ("type", Lean.toJson (toString printed)),
      ("axioms", Lean.toJson (axioms.toList.map Lean.Name.toString))]
    Lean.logInfo m!"DERAND-AXIOMS {row.compress}"
    count := count + 1
  Lean.logInfo m!"DERAND-AXIOM-COUNT {count}"

#print axioms Complexity.exists_seedMajorityTM
#print axioms Complexity.seedMajority_mem_DTIME
#print axioms TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp
#print axioms Complexity.IterateFind.polyTimeComputable_find
#print axioms Complexity.polyTimeComputable_iterateFind
#print axioms Complexity.IterateFind.computesFunInTime_find
#print axioms Complexity.mem_DTIME_iff
#print axioms Turing.FinTM.decidesInTime_iff
#check @Complexity.IterateFind.computesFunInTime_find
#check @Complexity.mem_DTIME_iff
#check @Turing.FinTM.decidesInTime_iff
