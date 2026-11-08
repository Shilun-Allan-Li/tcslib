<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.queryTrace_eq_of_agreeOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trace Determined by Available Coordinates

**Claim.** If two inputs agree on every coordinate in a tree's available set, then the tree has the same query trace on both inputs.

**Proof.** Proceed by induction on the tree. At a leaf both traces are empty. At a query node, its coordinate belongs to the available set, so the inputs agree there and select the same child. The remaining tree has the original available set with that coordinate erased; agreement on this smaller set follows from agreement on the original set. The induction hypothesis gives equal traces for the selected child, and adding the common queried coordinate at the front yields equal traces for the original tree.
