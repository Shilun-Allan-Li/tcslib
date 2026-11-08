<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaPolynomialHypothesis_ideal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ideal Low-Degree Junta Hypothesis

**Claim.** The low-degree learner applied to the restricted labeled batch returns the same hypothesis as when it is applied to the reindexed inputs labeled by the reindexed restriction, using the prescribed degree bound and polynomial sample count.

**Proof.** By the identity for the reindexed polynomial samples ( `lowDegreeJuntaPolynomialSamples_ideal`), each sample selected from the restricted labeled batch is exactly the corresponding reindexed input paired with the reindexed restriction's output at that input. The polynomial hypothesis is defined by applying the low-degree learner to those samples. Substituting the sample identity into this definition gives the stated equality of learner outputs.

**Key facts.** `FABL.lowDegreeJuntaPolynomialSamples_ideal`.
