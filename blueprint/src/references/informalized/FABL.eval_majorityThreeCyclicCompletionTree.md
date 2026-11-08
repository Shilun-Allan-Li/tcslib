<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.eval_majorityThreeCyclicCompletionTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cyclic Completion Tree Evaluation

**Claim.** For a sign alphabet, seed, known sign, and sign vector on three coordinates, the completion tree evaluates to the known sign when it agrees with the vector at the second cyclic coordinate, and otherwise returns the value at the third cyclic coordinate.

**Proof.** The tree first queries the second cyclic coordinate. If its value equals the known sign, the chosen branch is the leaf labelled by that sign, so evaluation returns it. If the values differ, the branch queries the third cyclic coordinate and returns the value found there. These two cases are precisely the definition of the stated pair-value rule.
