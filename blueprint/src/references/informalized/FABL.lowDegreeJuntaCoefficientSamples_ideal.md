<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.lowDegreeJuntaCoefficientSamples_ideal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ideal Coefficient Samples Under Reindexing

**Claim.** For each frequency in the stated family, the batch of reindexed labeled samples agrees pointwise with the pairs formed from each corresponding reindexed input and the value of the reindexed restricted function at that input.

**Proof.** Fix a sample index. Reindexing its free-coordinate assignment by the inverse of the fixed-sign-cube equivalence produces the corresponding input in the reindexed cube. Its label in the original batch is the restricted function evaluated at that assignment. By the definition of the reindexed restricted function, this label is exactly the reindexed restricted function evaluated at the reindexed input. Hence the two pairs agree at every index, and therefore the sample batches agree pointwise.
