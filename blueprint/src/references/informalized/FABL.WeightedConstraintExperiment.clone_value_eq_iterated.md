<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.clone_value_eq_iterated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cloned value as an iterated expectation

**Claim.** The cloned experiment’s value equals the expectation over original outcomes of the uniform mean of the cloned payoff over clone choices for that outcome’s query positions.

**Proof.** The cloned law first samples an original outcome and then maps a uniformly sampled function of clone choices at its query positions into a cloned outcome. The expectation under this two-stage law is the iterated expectation over the original outcome law and the conditional clone law (`pmfExpectation_bind`). For each fixed outcome, the map into cloned outcomes does not change the expectation when the payoff is pulled back (`pmfExpectation_map`). The conditional law is uniform, so its expectation is precisely the uniform mean over clone choices (`pmfExpectation_uniformPMF_eq_expect`). This is the stated formula.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
