<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.RestrictedWeightInput.outerInput_biasParameter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outer Input Bias Ratio

**Claim.** The outer input's accuracy parameter divided by its Fourier bound equals the original accuracy parameter divided by four times the square of its Fourier bound.

**Proof.** The outer input uses the quarter-bias input and has Fourier bound equal to the square of the original bound. The quarter-bias accuracy equals one quarter of the original accuracy (`FABL.RestrictedWeightInput.quarterBias_epsilon`). Substituting these expressions into the outer ratio and simplifying yields the claimed equality.

**Key facts.** `FABL.RestrictedWeightInput.quarterBias_epsilon`.
