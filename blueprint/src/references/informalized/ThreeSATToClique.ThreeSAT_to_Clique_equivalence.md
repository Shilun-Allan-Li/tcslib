<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/ThreeSATToClique.lean :: ThreeSATToClique.ThreeSAT_to_Clique_equivalence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# 3-SAT and clique equivalence

**Claim.** A 3-CNF formula is satisfiable if and only if its conflict graph has a clique whose size equals the number of clauses.

**Proof.** Apply completeness of the reduction to obtain a clique of the required size from any satisfying assignment. Conversely, apply soundness of the reduction to obtain a satisfying assignment from any such clique. These two implications give the equivalence.

**Key facts.** `ThreeSATToClique.ThreeSAT_to_Clique_completeness`, `ThreeSATToClique.ThreeSAT_to_Clique_soundness`.
