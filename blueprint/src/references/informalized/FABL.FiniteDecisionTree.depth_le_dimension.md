<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.depth_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth bounded by dimension

**Claim.** For a finite alphabet, a decision tree with all $n$ coordinates initially available has depth at most $n$.

**Proof.** The depth bound for a tree with available set $A$ gives depth at most $|A|$ (`FABL.FiniteDecisionTree.depth_le_card_available`). Here the available set is the full set of coordinates, whose cardinality is $n$. Therefore the depth is at most $n$.

**Key facts.** `FABL.FiniteDecisionTree.depth_le_card_available`.
