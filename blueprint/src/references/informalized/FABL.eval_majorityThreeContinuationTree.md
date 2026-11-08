<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.eval_majorityThreeContinuationTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuation Tree Evaluation

**Claim.** The continuation tree evaluates to the majority-pair value of its first two signs and the output of its third tree.

**Proof.** If the first two signs agree, the continuation tree is a leaf labeled by their common sign, which is the majority-pair value regardless of the third tree's output. If they differ, the continuation tree is the third tree itself, so its evaluation is the third output, again exactly the majority-pair value. These two cases prove the formula.
