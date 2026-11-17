<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.RestrictedWeightInput.outerCount_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Outer Sample Count

**Claim.** For every restricted-weight input, the sample count associated with its outer input is positive.

**Proof.** The outer input is a small-bias Fourier input, whose sample count is positive by the sample-count positivity theorem (`FABL.SmallBiasFourierInput.sampleCount_pos`). Since the outer count is defined as that sample count, it too is positive.

**Key facts.** `FABL.SmallBiasFourierInput.sampleCount_pos`.
