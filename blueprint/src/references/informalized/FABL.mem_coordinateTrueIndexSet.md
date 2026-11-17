<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.mem_coordinateTrueIndexSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True-coordinate membership

**Claim.** An index belongs to the true-coordinate index set exactly when its Boolean string has value true at coordinate $j$.

**Proof.** By definition, the set consists of all indices in the full index set that pass the filter requiring their Boolean string to have value true at coordinate $j$. Since $i$ is already an index in that full set, membership is equivalent to precisely this filter condition.
