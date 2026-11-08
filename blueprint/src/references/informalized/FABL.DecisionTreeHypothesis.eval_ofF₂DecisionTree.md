<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DecisionTreeHypotheses.lean :: FABL.DecisionTreeHypothesis.eval_ofF₂DecisionTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Preserved by Conversion

**Claim.** For a finite-coordinate decision tree with sign-valued leaves, converting it to a decision-tree hypothesis preserves its value at every binary input.

**Proof.** Proceed by induction on the tree. At a leaf, both the converted tree and the original tree return the stored value. At a query node, conversion retains the queried coordinate and converts each child. Both evaluations therefore inspect the same input coordinate and follow the same branch: if its value is zero, the zero child is used; otherwise, the one child is used. The induction hypothesis identifies the converted child’s value with the original child’s value in either case, proving equality at the query node.
