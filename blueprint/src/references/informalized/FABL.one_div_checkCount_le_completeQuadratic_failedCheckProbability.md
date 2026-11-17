<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.one_div_checkCount_le_completeQuadratic_failedCheckProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound on Check Failure Probability

**Claim.** If at least one of the $3n+3$ checks fails, then a uniformly chosen check fails with probability at least $1/(3n+3)$.

**Proof.** The seed set consists of two endpoint checks and three checks for each of the $n$ transitions, so it has cardinality $3n+3$. The given failing seed witnesses that the predicate “this check fails” holds for at least one seed. The uniform probability of any predicate holding at a specified sample is at least the reciprocal of the sample space's cardinality (`FABL.one_div_card_le_uniformProbability_of_mem`). Applying this fact to the failing-seed predicate gives the claimed bound.

**Key facts.** `FABL.one_div_card_le_uniformProbability_of_mem`.
