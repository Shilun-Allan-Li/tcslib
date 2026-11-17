<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.F₂DecisionTree.computesJuntaRestriction_leaf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leaf computes a constant restriction

**Claim.** If the restriction of the target to the fixed assignment is constantly the sign $v$, then the leaf labelled $v$ computes the target on every input matching that assignment.

**Proof.** Fix a binary input $x$ whose sign encoding matches the assignment on $P$. Extract the free-coordinate part of that sign encoding. By the free-part reconstruction fact (`combineJuntaAssignment_freePart_of_matches`), combining this part with the fixed assignment recovers the original encoded input. Applying the hypothesis that the restriction is constantly $v$ to this free part therefore says that the target at the original encoded input equals $v$. A leaf evaluates to its label on every input, so its output agrees with the target, as required.

**Key facts.** `FABL.combineJuntaAssignment_freePart_of_matches`.
