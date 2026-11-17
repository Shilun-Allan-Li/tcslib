<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.card_querySet_eq_queryCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query trace cardinality

**Claim.** For a finite decision tree and input, the number of distinct coordinates queried equals the length of its query trace.

**Proof.** The query trace has no repeated coordinates, by the fact that each query removes its coordinate from the set available to all later queries (`FABL.FiniteDecisionTree.queryTrace_nodup`). For a list with no repetitions, converting it to a finite set preserves its length as cardinality. Since the query set is exactly the finite set of entries in the trace, its cardinality equals the trace length, which is the query count by definition.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_nodup`.
