<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.RestrictedWeightInput.innerInput_biasParameter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner Input Bias Ratio

**Claim.** The inner input's accuracy parameter divided by its Fourier bound equals the original accuracy parameter divided by four times the original Fourier bound.

**Proof.** The inner input uses the quarter-bias input and retains the original Fourier bound. The quarter-bias accuracy is one quarter of the original accuracy (`FABL.RestrictedWeightInput.quarterBias_epsilon`). Substituting this into the ratio and simplifying gives the stated equality.

**Key facts.** `FABL.RestrictedWeightInput.quarterBias_epsilon`.
