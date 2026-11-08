<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.zeroDimensionExactSparseSpectrumLearner_evaluate_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exactness in Zero Dimensions

**Claim.** If $n$ is a natural number with $\neg(0<n)$, then for every Boolean function on the $n$-dimensional sign cube, the hypothesis returned by the zero-dimensional exact sparse-spectrum learner agrees with the target at every input.

**Proof.** The learner makes one query at the all-one input and returns the constant sparse Fourier hypothesis whose value is the answer to that query. The execution result is therefore that constant hypothesis (`runWithCost_zeroDimensionExactSparseSpectrumLearner`). A constant sparse Fourier hypothesis evaluates to the constant function with its chosen sign (`constantSparseFourierHypothesis_evaluate`). Since $n$ is a natural number and is not positive, $n=0$. The zero-dimensional cube has only one point, so the queried all-one input is that point; hence the target's value there is its value at every input. The returned constant function consequently agrees with the target everywhere.

**Key facts.** `FABL.runWithCost_zeroDimensionExactSparseSpectrumLearner`, `FABL.constantSparseFourierHypothesis_evaluate`.
