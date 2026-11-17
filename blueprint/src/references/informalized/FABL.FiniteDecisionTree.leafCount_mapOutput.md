<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.FiniteDecisionTree.leafCount_mapOutput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leaf Count Under Output Mapping

**Claim.** Applying any map to every leaf label of a finite decision tree preserves its number of leaves.

**Proof.** Induct on the tree. At a leaf, mapping the label leaves the leaf count equal to one. At a query, mapping the output applies the same operation independently to every child, while the leaf count is the sum of the child leaf counts over all alphabet symbols. By the induction hypothesis, each corresponding child has unchanged leaf count, so the sums agree.
