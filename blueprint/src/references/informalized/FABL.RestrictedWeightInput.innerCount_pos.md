<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.RestrictedWeightInput.innerCount_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Inner Sample Count

**Claim.** For every restricted-weight input, the associated inner sample count is positive.

**Proof.** The inner input is a small-bias Fourier input, so its sample count is positive by the positivity theorem for sample counts (`FABL.SmallBiasFourierInput.sampleCount_pos`). The inner count is defined to be exactly that sample count, giving the result.

**Key facts.** `FABL.SmallBiasFourierInput.sampleCount_pos`.
