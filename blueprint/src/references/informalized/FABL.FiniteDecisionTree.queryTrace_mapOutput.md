<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.queryTrace_mapOutput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trace Under Leaf Relabeling

**Claim.** Replacing every leaf label of a finite decision tree by its image under $g$ leaves the query trace unchanged on every input.

**Proof.** Proceed by induction on the tree. For a leaf, both traces are empty. At a query node, relabeling preserves the queried coordinate and the input value still selects the corresponding child. The induction hypothesis gives equal traces for that child, so prefixing the common queried coordinate gives equal traces at the node.
