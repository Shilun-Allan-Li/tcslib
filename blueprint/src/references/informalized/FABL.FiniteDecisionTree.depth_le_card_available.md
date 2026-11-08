<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.FiniteDecisionTree.depth_le_card_available -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth bounded by available coordinates

**Claim.** For a finite alphabet, the maximum number of queries along any path of a decision tree with available coordinate set $A$ is at most $|A|$.

**Proof.** Proceed by induction on the tree. A leaf has depth zero, which is at most the cardinality of the available set. For a query at coordinate $i$, every child has available set $A\setminus\{i\}$. By the induction hypothesis, each child's depth is at most the cardinality of that set, so the supremum of the child depths is also at most $|A\setminus\{i\}|$. The tree's depth is that supremum plus one. Because $i\in A$, removing it decreases the cardinality by one, and hence the tree's depth is at most $|A|$.
