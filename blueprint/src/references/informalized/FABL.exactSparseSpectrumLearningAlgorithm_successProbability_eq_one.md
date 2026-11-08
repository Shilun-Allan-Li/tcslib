<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumLearningAlgorithm_successProbability_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Learning Success

**Claim.** For every target in the exact sparse spectrum concept class, the learner outputs a hypothesis that agrees with the target everywhere; hence its success probability is one for every allowed accuracy.

**Proof.** The exact reconstruction theorem (`exactSparseSpectrumLearner_evaluate_eq`) says that, under the sparsity hypothesis, the learner's output evaluates to the target at every input. The deterministic query program induces a point mass on its run and cost (`runWithCost_exactSparseSpectrumLearningProgram`). Thus the success probability is the probability, under that point mass, that the relative Hamming distance is at most the requested accuracy. The output agrees everywhere, so this distance is zero. Since the accuracy is nonnegative, the event holds for the unique outcome of the point mass, and its probability is one.

**Key facts.** `FABL.exactSparseSpectrumLearner_evaluate_eq`, `FABL.runWithCost_exactSparseSpectrumLearningProgram`.
