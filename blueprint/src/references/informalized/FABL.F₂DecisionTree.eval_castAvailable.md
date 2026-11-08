<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.F₂DecisionTree.eval_castAvailable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation under Reindexing

**Claim.** If the available coordinate sets $A$ and $B$ are equal, regarding a tree on $A$ as a tree on $B$ preserves its value at every input.

**Proof.** Since $A=B$, replacing $B$ by $A$ turns the cast into the identity tree. Its evaluation is therefore unchanged.
