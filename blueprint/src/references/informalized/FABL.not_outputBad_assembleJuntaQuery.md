<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.not_outputBad_assembleJuntaQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Combining Successful Junta Restrictions

**Claim.** If each optional branch tree is either absent or correctly computes the corresponding restriction of the target, then the assembled optional query tree is either absent or correctly computes the restriction specified by the original assignment.

**Proof.** If either branch is absent, the assembled tree is absent by definition, so it is not bad. Suppose both branches are present. The hypotheses that neither branch is bad imply, by the fact that a present nonbad tree computes its restriction (`FABL.computesJuntaRestriction_of_not_outputBad`), that each branch computes the restriction for its respective extended assignment. Consider an input matching the original assignment. If its value at coordinate $i$ is $0$, the query tree follows the zero branch. The input matches the zero-extended assignment: the characterization of matching an inserted assignment says this is equivalent to matching the original assignment and having the prescribed value at $i$ (`FABL.matches_insertJuntaFixedAssignment_iff`). Thus the zero branch returns the target value. If the input value at $i$ is nonzero, it equals $1$, since the cube has only the two elements of $\mathbb F_2$. The same argument with the one-extended assignment shows that the one branch returns the target value. Casting either branch to the query tree's available-coordinate set does not change its evaluation (`FABL.F₂DecisionTree.eval_castAvailable`). Hence the assembled query tree computes the original restriction, so it is not bad.

**Key facts.** `FABL.computesJuntaRestriction_of_not_outputBad`, `FABL.matches_insertJuntaFixedAssignment_iff`, `FABL.F₂DecisionTree.eval_castAvailable`.
