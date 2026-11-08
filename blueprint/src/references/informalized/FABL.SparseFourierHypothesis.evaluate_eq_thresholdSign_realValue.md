<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LearningModel.lean :: FABL.SparseFourierHypothesis.evaluate_eq_thresholdSign_realValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation as a threshold sign

**Claim.** For every sign vector, the evaluation of a sparse Fourier hypothesis is $1$ when its real-valued Fourier sum is nonnegative, and $-1$ otherwise.

**Proof.** Fix a sign vector $x$. By the rational-to-real value identity (`FABL.SparseFourierHypothesis.value_cast_eq_realValue`), the rational sum defining the hypothesis’s value, regarded as real, equals its real Fourier sum at $x$. Thus the condition that the rational value is nonnegative is equivalent to the condition that the real sum is nonnegative. Both evaluation and the threshold sign return $1$ in that case and $-1$ otherwise, so they agree at every $x$ and hence are the same function.

**Key facts.** `FABL.SparseFourierHypothesis.value_cast_eq_realValue`.
