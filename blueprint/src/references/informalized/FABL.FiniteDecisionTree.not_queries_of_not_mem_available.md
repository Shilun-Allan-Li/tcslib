<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.FiniteDecisionTree.not_queries_of_not_mem_available -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Queries Stay in the Available Set

**Claim.** Every coordinate in the query trace belongs to the tree's available coordinate set; consequently, a coordinate outside that set never appears in the trace.

**Proof.** Suppose a coordinate $i$ appears in the query trace. The trace-subset property says that every coordinate appearing in the trace belongs to the available set (`queryTrace_subset_available`). Thus, if $i$ is outside that set, it cannot appear in the trace.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_subset_available`.
