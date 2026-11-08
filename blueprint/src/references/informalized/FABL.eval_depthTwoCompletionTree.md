<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.eval_depthTwoCompletionTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Completion Tree

**Claim.** For a block, seed, known sign, and input, the depth-two completion tree evaluates to the majority-pair value formed from the known sign and the input signs at the two cyclically chosen remaining coordinates of that block.

**Proof.** The completion tree is obtained by reindexing the three-coordinate cyclic completion tree along the embedding of the chosen block into the nine input coordinates. Evaluation commutes with this reindexing: it is the evaluation of the original tree on the input restricted along the embedding (`FABL.FiniteDecisionTree.eval_reindex`). The cyclic completion tree evaluates to the majority-pair value of its supplied known sign and the two corresponding queried signs (`FABL.eval_majorityThreeCyclicCompletionTree`). By the definitions of the block embedding and recursive input block, those queried signs are exactly the two displayed coordinates of the block. This gives the claimed evaluation.

**Key facts.** `FABL.FiniteDecisionTree.eval_reindex`, `FABL.eval_majorityThreeCyclicCompletionTree`.
