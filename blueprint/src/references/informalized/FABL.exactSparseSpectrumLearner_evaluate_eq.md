<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumLearner_evaluate_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Learner Recovery

**Claim.** For a Boolean function on the sign cube whose corresponding function on $\mathbb F_2^n$ has at most $2^{k+1}$ nonzero Fourier coefficients, the exact sparse-spectrum learner returns a hypothesis that evaluates to the target at every input.

**Proof.** Split into the two possibilities for the dimension. If $n>0$, the learner is its positive-dimensional version, and the positive-dimensional recovery theorem (`positiveExactSparseSpectrumLearner_evaluate_eq`) gives the desired equality under the stated sparsity bound. If $n$ is not positive, then, since $n$ is natural, $n=0$; the learner is its zero-dimensional version, and the zero-dimensional recovery theorem (`zeroDimensionExactSparseSpectrumLearner_evaluate_eq`) gives the equality directly. These cases exhaust all dimensions.

**Key facts.** `FABL.positiveExactSparseSpectrumLearner_evaluate_eq`, `FABL.zeroDimensionExactSparseSpectrumLearner_evaluate_eq`.
