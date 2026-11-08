<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.eval_depthTwoInitialTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Query Tree Evaluation

**Claim.** The initial query tree for a block and seed evaluates to the input sign at the coordinate assigned to that block and seed.

**Proof.** The initial tree consists of one query at the designated coordinate, with a leaf labeled by whichever sign is returned by that query. Evaluating it therefore returns exactly the input sign at that coordinate.
