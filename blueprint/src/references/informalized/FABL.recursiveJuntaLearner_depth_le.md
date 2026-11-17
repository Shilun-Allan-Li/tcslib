<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.recursiveJuntaLearner_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Bound for the Recursive Learner

**Claim.** If a supported outcome of the recursive learner on $f$ returns a decision tree $T$, then the depth of $T$ is at most $k$.

**Proof.** The learner’s output is a map of the auxiliary learner’s output, so support under the mapped run provides a supported auxiliary outcome whose output maps to the given tree (`FABL.LearningProgram.runWithCost_map`). If that auxiliary output were absent, its mapped output would also be absent, contrary to the hypothesis that the given tree is returned. Thus the auxiliary outcome contains a tree, and the output equality identifies the given tree with its cast to the full coordinate set. This cast preserves depth (`FABL.F₂DecisionTree.depth_castAvailable`). Apply the auxiliary depth bound at fuel $k$, with the learner’s per-call failure parameter, empty fixed-coordinate set, and empty assignment; it gives depth at most $k$.

**Key facts.** `FABL.LearningProgram.runWithCost_map`, `FABL.F₂DecisionTree.depth_castAvailable`, `FABL.recursiveJuntaLearnerAux_depth_le`.
