<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.constantSparseFourierHypothesis_evaluate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Constant Sparse Fourier Hypothesis

**Claim.** For any dimension and sign value, evaluating the sparse Fourier hypothesis with its sole coefficient at the empty set equal to that sign gives the constant function with that value.

**Proof.** Rewrite evaluation as thresholding the real-valued sparse Fourier sum, using the evaluation formula (SparseFourierHypothesis.evaluate_eq_thresholdSign_realValue). At any input, the support consists only of the empty set, so the sum has one term: the coefficient, which is the real image of the chosen sign, multiplied by the empty monomial. The empty monomial is $1$, leaving just that real sign value. A sign is either $1$ or $-1$; thresholding either value returns that same sign. Thus the evaluation is constant with the prescribed value.

**Key facts.** `FABL.SparseFourierHypothesis.evaluate_eq_thresholdSign_realValue`.
