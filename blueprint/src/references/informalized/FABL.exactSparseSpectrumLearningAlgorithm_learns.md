<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumLearningAlgorithm_learns -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Sparse Spectrum Learning

**Claim.** For every dimension $n$, sparsity parameter $k$, and learning accuracy, the exact sparse spectrum learning algorithm learns the corresponding concept class with the required success probability.

**Proof.** Fix a target in the concept class and an accuracy. The theorem that the algorithm’s success probability is exactly one on every target in this class ( `FABL.exactSparseSpectrumLearningAlgorithm_successProbability_eq_one`) applies directly. Since $1\ge 9/10$, the defining success-probability requirement for learning the class holds.

**Key facts.** `FABL.exactSparseSpectrumLearningAlgorithm_successProbability_eq_one`.
