<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.F₂DecisionTree.eval_mapOutputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation after Mapping Outputs

**Claim.** Applying a function $g$ to every leaf output and then evaluating gives $g$ applied to the original tree's evaluation.

**Proof.** Proceed by induction on the tree. For a leaf, mapping its output gives exactly $g$ of the original leaf's value. At a query, both the mapped tree and the original tree inspect the same coordinate and therefore choose the same branch. The induction hypothesis for that child identifies the mapped child's evaluation with $g$ of the original child's evaluation, proving the claim in either branch.
