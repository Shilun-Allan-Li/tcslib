<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.deterministicRestrictedWeight_work_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work asymptotic bound

**Claim.** As the restricted-weight task scale tends to infinity, the work component of the deterministic restricted-weight cost is big-O of the eighth power of one plus that scale.

**Proof.** For every task, the resource-bounds result gives work at most the polynomial budget $2^{20}(\text{scale}+1)^8$. The work and comparison function are natural-number casts in the stated asymptotic bound, whose norms are their values. Casting the pointwise inequality to the reals therefore gives the uniform bound with constant $2^{20}$, which establishes the big-O statement along the filter induced by task scale.

**Key facts.** `FABL.deterministicRestrictedWeightCost_resource_bounds`.
