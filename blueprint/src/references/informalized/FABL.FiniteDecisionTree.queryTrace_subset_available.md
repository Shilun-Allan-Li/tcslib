<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.queryTrace_subset_available -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Queries Stay Within the Available Set

**Claim.** Every coordinate appearing in the query trace of a tree belongs to that tree’s available set.

**Proof.** Proceed by induction on the tree, fixing the input. At a leaf the trace is empty, so the assertion holds. At a query node with coordinate $i$, the trace starts with $i$, which belongs to the available set by the node’s hypothesis. Every later coordinate belongs, by the induction hypothesis for the selected child, to the child’s available set: the original available set with $i$ erased. Hence it also belongs to the original set.
