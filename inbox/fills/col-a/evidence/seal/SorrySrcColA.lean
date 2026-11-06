import TCSlib.Cryptography.ZeroKnowledge.NP
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Simulator
open Lean Elab Command

/-- For each consumer, the declarations in its dependency closure whose own value mentions
`sorryAx` (the sources of the `sorryAx` in its axiom print). -/
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

#eval show CommandElabM Unit from do
  let env ← getEnv
  for r in [``TCSlib.Cryptography.col_zeroKnowledgeProof, ``TCSlib.Cryptography.zk_proof_of_levinReduction,
      ``TCSlib.Cryptography.zk_proof_of_owp_levinReduction,
      ``TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction,
      ``TCSlib.Cryptography.zk_proof_of_witnessRelation, ``TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp,
      ``TCSlib.Cryptography.zk_proof_of_mem_NP, ``TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp,
      ``TCSlib.Cryptography.colRep_efficientProverProof, ``TCSlib.Cryptography.R3COL_witnessRelation] do
    IO.println s!"{r}: sorry sources {sorrySources env r}"
