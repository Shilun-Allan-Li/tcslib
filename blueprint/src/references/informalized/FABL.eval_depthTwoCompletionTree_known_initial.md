<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.eval_depthTwoCompletionTree_known_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion Tree with a Known Initial Value

**Claim.** For a block, seed, and nine-coordinate sign assignment, the completion tree supplied with the sign at its initial coordinate evaluates to the majority of the three signs in that block.

**Proof.** The completion-tree evaluation formula expresses the result as the majority-pair value of the supplied initial sign and the signs at the second and third cyclic coordinates. The cyclic majority tree computes three-bit majority (`FABL.majorityThreeCyclicTree_computes`), and its evaluation formula identifies its output with that same majority-pair value on the three coordinates (`FABL.eval_majorityThreeCyclicTree`). Taking the supplied initial sign to be the input at the first cyclic coordinate therefore makes the completion-tree output equal to the majority of the block's three signs.

**Key facts.** `FABL.eval_depthTwoCompletionTree`, `FABL.eval_majorityThreeCyclicTree`, `FABL.majorityThreeCyclicTree_computes`.
