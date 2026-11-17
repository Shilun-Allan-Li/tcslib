<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.recursiveJuntaLearnerAux_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive Tree Depth Bound

**Claim.** For any fuel $r$, fixed-coordinate set $P$, and assignment on $P$, every supported outcome of the recursive learner that returns a decision tree has depth at most $r$.

**Proof.** We argue by induction on the fuel, tracking supported outcomes of the run and the tree they return. At fuel zero, the learner maps the node finder’s decision to a tree only when the decision is a constant; that output is a leaf, of depth zero. A missing or relevant-coordinate decision yields no tree, so there is nothing to prove. For the induction step, a missing decision again returns no tree, while a constant decision returns a leaf, whose depth is at most the positive fuel. If the finder selects a relevant coordinate, the run proceeds through the two recursive calls, one for each sign assigned to that coordinate. A supported outcome returning a tree must have supported tree outcomes from both calls: otherwise assembling the children returns no tree. By the induction hypothesis, each child has depth at most the preceding fuel. The assembled tree queries the selected coordinate above those children; its depth is one plus the maximum child depth. Hence its depth is at most one plus the preceding fuel, as required. Changing the available-coordinate index set by the casts used in assembly does not change a child’s depth (`FABL.F₂DecisionTree.depth_castAvailable`). The support analysis follows the run of mapped and bound programs, whose distributions are described by `FABL.LearningProgram.runWithCost_map` and `FABL.LearningProgram.runWithCost_bind`.

**Key facts.** `FABL.LearningProgram.runWithCost_bind`, `FABL.LearningProgram.runWithCost_map`, `FABL.F₂DecisionTree.depth_castAvailable`.
