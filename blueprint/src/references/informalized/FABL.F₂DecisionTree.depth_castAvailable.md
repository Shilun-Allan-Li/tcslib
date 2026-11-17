<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.F₂DecisionTree.depth_castAvailable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth invariance under reindexing

**Claim.** If two available coordinate sets are equal, reindexing a decision tree from one set to the other leaves its depth unchanged.

**Proof.** Because the two coordinate sets are equal, replacing the second set by the first reduces the reindexing to the identity. The resulting tree is the original tree, so their depths agree.
