<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.sum_queryIndicator_eq_queryCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Indicators Count the Trace

**Claim.** For a finite-alphabet decision tree on all $n$ coordinates and any input, summing the indicators of whether each coordinate occurs in the query trace gives the query count.

**Proof.** The sum of the indicators over coordinates is the cardinality of the set of coordinates whose indicators are one. That set is exactly the tree's query set on the input, by the definitions of queries and the query set. The cardinality of this query set equals the length of the query trace (`card_querySet_eq_queryCount`), which is the query count.

**Key facts.** `FABL.FiniteDecisionTree.card_querySet_eq_queryCount`.
