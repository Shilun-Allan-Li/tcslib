<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.exactDegreeFourierEstimatorOutput_evaluate_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact estimator evaluation

**Claim.** Under the stated degree and sample-accuracy hypotheses, thresholding the estimator's sparse Fourier hypothesis recovers the target Boolean function at every input.

**Proof.** The estimator's real-valued sparse Fourier sum equals the target's real-valued sign representation by the real-valued recovery theorem (FABL.exactDegreeFourierEstimatorOutput_realValue_eq). The thresholding identity for sparse hypotheses (FABL.SparseFourierHypothesis.evaluate_eq_thresholdSign_realValue) therefore identifies the estimator's output with the thresholded target sign representation. At each input, the target's sign value is either $-1$ or $1$; thresholding either value returns that same sign. Finally, the sign-value map is injective (FABL.signValue_injective), so equality of sign values yields equality of the Boolean-function outputs.

**Key facts.** `FABL.SparseFourierHypothesis.evaluate_eq_thresholdSign_realValue`, `FABL.exactDegreeFourierEstimatorOutput_realValue_eq`, `FABL.signValue_eq_neg_one_or_one`, `FABL.signValue_injective`.
