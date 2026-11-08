<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.RestrictedWeightInput.quarterBias_epsilon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Accuracy of the Quarter Bias

**Claim.** For a restricted-weight input, the accuracy parameter of its quarter-bias input equals one quarter of the original accuracy parameter.

**Proof.** The original bias denominator is positive: the numerator is positive, and twice the numerator is at most the denominator. Hence its image in the real numbers is nonzero. The quarter-bias input keeps the numerator and multiplies the denominator by four, so its accuracy is the original numerator divided by four times the original denominator. Since the denominator is nonzero, this is one quarter of the original accuracy.
