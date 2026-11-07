import TCSlib.Cryptography.Candidates
import TCSlib.Cryptography.ZeroKnowledge
import TCSlib.Cryptography.ZeroKnowledge.NP
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring
open Lean Meta Elab Command

-- Fill targets and headlines (post-landing base aa276ae8)
open TCSlib.Cryptography TCSlib.Cryptography.Candidates in
section
-- #224 discrete log
#print axioms dlCollection_oneWay
#print axioms fullDLCollection_hardCore
#print axioms elGamal_secure
-- #226 factoring / RSA / Rabin
#print axioms factoringCollection_oneWay
#print axioms rsaCollection_oneWay
#print axioms rsa_imp_factoring
#print axioms rsaTrapdoor_oneWay
#print axioms rabinCollection_oneWay
#print axioms rabinBlumTrapdoor_oneWay
#print axioms blumFactoring_of_factoring
#print axioms blumFactoring_of_rabinBlum_oneWay
-- #225 three-colouring
#print axioms col_zk
#print axioms col_hvzk
#print axioms R3COL_witnessRelation
#print axioms colRep_efficientProverProof
#print axioms colRep_interactiveProof
#print axioms col_zeroKnowledgeProof
-- NP.lean wrappers
#print axioms LevinReduction.zk
#print axioms LevinReduction.efficientProverProof
#print axioms LevinReduction.efficientProverProofErr
#print axioms zk_proof_of_levinReduction
#print axioms zk_proof_of_owp_levinReduction
#print axioms exists_commitment_zk_proof_of_owp_levinReduction
#print axioms zk_proof_of_witnessRelation
#print axioms zk_proof_of_witnessRelation_of_owp
#print axioms zk_proof_of_mem_NP
#print axioms zk_proof_of_mem_NP_of_owp
end

def C : Name := `TCSlib.Cryptography.Candidates
def TC : Name := `TCSlib.Cryptography.ZeroKnowledge.ThreeColoring
def sweepMods : List Name :=
  [C ++ `Concrete, C ++ `DiscreteLog, C ++ `DiscreteLogHardcore, C ++ `ElGamal,
   C ++ `Factoring, C ++ `RSA, C ++ `Rabin,
   TC ++ `Language, TC ++ `Machines, TC ++ `Parties, TC ++ `ProtocolProofs,
   TC ++ `ColRepWitness, TC ++ `ColRepSound, TC ++ `Protocol, TC ++ `SimulatorLemmas,
   TC ++ `ColZKLemmas, TC ++ `SimulatorNumeric, TC ++ `SimulatorMachine, TC ++ `ColZKMachine,
   TC ++ `Simulator, `TCSlib.Cryptography.ZeroKnowledge.NP]

/-- The declarations in a constant's closure whose own type or value mentions `sorryAx`. -/
def sorrySources (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[root]
  let mut out := #[]
  while !todo.isEmpty do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let used := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants) |>.getD #[])
    if used.contains ``sorryAx then out := out.push c
    for u in used do
      if !seen.contains u then todo := todo.push u
  return out

elab "#axsweep" : command => do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut tot : Nat := 0
  let mut totPub : Nat := 0
  let mut totBad : Nat := 0
  for mn in sweepMods do
    let some idx := env.getModuleIdx? mn | do logInfo m!"MISSING MODULE {mn}"; continue
    let mut ours : Array Name := #[]
    for (n, _) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n == some idx then ours := ours.push n
    let mut bad : Nat := 0
    let mut pub : Nat := 0
    for n in ours.qsort (fun a b => a.toString < b.toString) do
      if !isPrivateName n && !n.isInternal then pub := pub + 1
      let ax ← liftCoreM <| Lean.collectAxioms n
      let nonstd := ax.filter (fun a => !std.contains a)
      if nonstd.size > 0 then
        bad := bad + 1
        logInfo m!"AX-NONSTD {n} (private={isPrivateName n}): {ax.toList} SORRYSRC {sorrySources env n}"
    tot := tot + ours.size; totPub := totPub + pub; totBad := totBad + bad
    logInfo m!"SWEEP {mn}: {ours.size} constants ({pub} public, non-internal), non-standard: {bad}"
  logInfo m!"SWEEP TOTAL: {tot} constants ({totPub} public), non-standard: {totBad}"

#axsweep
