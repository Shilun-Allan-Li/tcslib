<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.queryTrace_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Repeated Queries in a Trace

**Claim.** For any finite decision tree and input, no coordinate occurs more than once in its query trace.

**Proof.** Proceed by induction on the tree. At a leaf the trace is empty, hence has no repetitions. At a query node, the trace consists of the queried coordinate followed by the trace of the child selected by the input value at that coordinate. By the availability property of query traces (`queryTrace_subset_available`), every coordinate in the child trace belongs to the child’s available set, which is the original available set with the current coordinate erased. Thus the current coordinate cannot occur in the child trace. The induction hypothesis says that the child trace itself has no repetitions, so adjoining the current coordinate preserves this property.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_subset_available`.
