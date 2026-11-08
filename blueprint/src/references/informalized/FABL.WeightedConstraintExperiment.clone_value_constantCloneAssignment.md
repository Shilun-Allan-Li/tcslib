<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.clone_value_constantCloneAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value under a constant clone assignment

**Claim.** If every clone of each variable is assigned the same value as that variable under an assignment to the original variables, the cloned experiment’s value equals the original experiment’s value.

**Proof.** Expand the cloned experiment’s value using its outcome law followed by uniform sampling of clone choices (`pmfExpectation_bind`). For a fixed original outcome, the constant clone assignment makes the value queried at every position equal to the original assignment at that position. Consequently the clone payoff is exactly the original payoff, independently of the sampled clone indices. The uniform mean of this constant payoff is the payoff itself (`pmfExpectation_map`, `pmfExpectation_uniformPMF_eq_expect`, and the fact that the expectation of a constant equals that constant). Averaging over original outcomes gives the original experiment’s value.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
