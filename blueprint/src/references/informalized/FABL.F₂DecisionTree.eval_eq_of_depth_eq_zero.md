<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.F₂DecisionTree.eval_eq_of_depth_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth-Zero Evaluation

**Claim.** A decision tree of depth zero has the same evaluation on every pair of inputs.

**Proof.** Case-split on the tree. A leaf returns its stored value independently of the input. In the query case, the depth is one plus the maximum of the depths of the two children, and so cannot equal zero. Thus the query case is impossible under the hypothesis, leaving only the leaf case.
