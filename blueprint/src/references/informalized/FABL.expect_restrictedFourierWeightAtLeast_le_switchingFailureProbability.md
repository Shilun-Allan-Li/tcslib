<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.expect_restrictedFourierWeightAtLeast_le_switchingFailureProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Fourier Weight Bound

**Claim.** When $0\le\delta\le1$, the expected restricted Fourier weight at degrees at least $k$ is bounded above by the switching-failure probability.

**Proof.** For each fixed restriction, the restricted Fourier weight at degrees at least $k$ is at most the indicator that the restricted decision-tree depth is at least $k$ (FABL.restrictedFourierWeightAtLeast_le_switchingFailureIndicator). Averaging this pointwise inequality over random restrictions preserves the inequality when $0\le\delta\le1$, by monotonicity of the random-restriction expectation (FABL.expectRandomRestriction_mono). The expectation of the indicator is precisely the switching-failure probability, giving the result.

**Key facts.** `FABL.restrictedFourierWeightAtLeast_le_switchingFailureIndicator`, `FABL.expectRandomRestriction_mono`.
