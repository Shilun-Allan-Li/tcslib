<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.deterministicRestrictedWeight_queries_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query count asymptotic bound

**Claim.** As the restricted-weight task scale tends to infinity, the membership-query count is big-O of the eighth power of one plus that scale.

**Proof.** For each task, the restricted-weight resource bounds give a pointwise upper bound on the query count by the polynomial budget, namely $2^{20}(Q+1-1)^8$, where $Q$ is one plus the task scale. Equivalently, the bound is $2^{20}(\text{scale}+1)^8$. This uniform pointwise estimate supplies the constant bound required by the definition of big-O along the filter induced by the task scale, with constant $2^{20}$.

**Key facts.** `FABL.deterministicRestrictedWeightCost_resource_bounds`.
