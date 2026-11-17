<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.expect_influence_extended_randomRestriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Under Random Restriction

**Claim.** For a real-valued function on the sign cube, the expected influence of coordinate $i$ under a $\delta$-random restriction is $\delta$ times its original influence.

**Proof.** Expand the expectation over restrictions as a finite sum over subsets $J$ of coordinates, weighted by their restriction probabilities. If $i\in J$, averaging the influence of the extended restriction over the fixed coordinates recovers the original influence (\texttt{expect_influence_extendedSignRestriction_of_mem}). If $i\notin J$, that influence is zero for every fixed assignment (\texttt{influence_extendedSignRestriction_of_not_mem}). Thus the sum reduces to the original influence multiplied by the total weight of subsets containing $i$. That total weight is $\delta$ (\texttt{sum_deltaRandomSubsetWeight_mem}), proving the formula.

**Key facts.** `FABL.expect_influence_extendedSignRestriction_of_mem`, `FABL.influence_extendedSignRestriction_of_not_mem`, `FABL.sum_deltaRandomSubsetWeight_mem`.
