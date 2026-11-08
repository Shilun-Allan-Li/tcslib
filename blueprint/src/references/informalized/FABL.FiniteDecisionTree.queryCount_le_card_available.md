<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.queryCount_le_card_available -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query count bounded by available coordinates

**Claim.** For any input, the number of queries made by a finite decision tree is at most the size of its available-coordinate set.

**Proof.** The query count equals the cardinality of the set of coordinates appearing in the query trace (\texttt{card_querySet_eq_queryCount}). Every coordinate in that trace belongs to the available set (\texttt{queryTrace_subset_available}), so the query set is a subset of the available set. Monotonicity of finite-set cardinality gives the bound.

**Key facts.** `FABL.FiniteDecisionTree.card_querySet_eq_queryCount`, `FABL.FiniteDecisionTree.queryTrace_subset_available`.
