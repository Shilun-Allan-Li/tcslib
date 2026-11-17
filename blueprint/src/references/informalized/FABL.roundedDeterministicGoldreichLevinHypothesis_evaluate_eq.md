<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.roundedDeterministicGoldreichLevinHypothesis_evaluate_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact recovery of the sign-valued target

**Claim.** If the family contains every subset whose target Fourier coefficient has magnitude at least the specified threshold, then the rounded hypothesis evaluates to the target at every point of the sign cube.

**Proof.** The rounded hypothesis evaluates as the threshold sign of its real-valued Fourier sum (`SparseFourierHypothesis.evaluate_eq_thresholdSign_realValue`). The real-valued sum equals the target's real-valued function (`roundedDeterministicGoldreichLevinHypothesis_realValue_eq`). At each point, the target's sign value is either $-1$ or $1$ (`signValue_eq_neg_one_or_one`), so taking its threshold sign returns that same value. Injectivity of the sign-value map (`signValue_injective`) then yields equality of the sign-valued functions.

**Key facts.** `FABL.SparseFourierHypothesis.evaluate_eq_thresholdSign_realValue`, `FABL.roundedDeterministicGoldreichLevinHypothesis_realValue_eq`, `FABL.signValue_eq_neg_one_or_one`, `FABL.signValue_injective`.
