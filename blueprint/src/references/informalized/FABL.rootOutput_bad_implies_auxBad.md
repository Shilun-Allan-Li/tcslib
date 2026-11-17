<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.rootOutput_bad_implies_auxBad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bad root output gives bad auxiliary output

**Claim.** If the root learner's optional output is bad for computing the target on the whole cube, then that output is bad for computing the target under the empty fixed-coordinate assignment.

**Proof.** Split according to whether the output is absent. If it is absent, the auxiliary notion declares it bad by definition. If it is a tree, suppose for contradiction it computes the target under the empty assignment. Every input matches the unique assignment on the empty coordinate set, since there are no coordinates to check. Thus the tree computes the target on every input. Casting its available-coordinate set does not change its evaluation (F₂DecisionTree.eval_castAvailable), so the root learner's mapped output computes the target everywhere, contradicting the assumed badness. Therefore the tree is bad under the empty assignment as well.

**Key facts.** `FABL.F₂DecisionTree.eval_castAvailable`.
