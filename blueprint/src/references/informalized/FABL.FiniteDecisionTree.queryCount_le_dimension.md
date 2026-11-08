<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.queryCount_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Count Bound

**Claim.** For a finite decision tree whose available coordinates are all of $\{0,\ldots,n-1\}$, the number of queries on any input is at most $n$.

**Proof.** The general bound on query count says that a tree using an available set $A$ makes at most $|A|$ queries (`queryCount_le_card_available`). Here the available set is the full set of coordinates, whose cardinality is $n$. Substituting this into the general bound gives the claim.

**Key facts.** `FABL.FiniteDecisionTree.queryCount_le_card_available`.
