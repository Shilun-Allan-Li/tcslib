<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.inputCost_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Cost and Dimension

**Claim.** For every input, the expected number of coordinates queried by a zero-error randomized decision tree on an $n$-coordinate input is at most $n$.

**Proof.** For each random seed, the selected deterministic tree queries at most $n$ coordinates, by the deterministic query-count bound (`FiniteDecisionTree.queryCount_le_dimension`). Thus each seed's query count, viewed as a real number, is at most $n$. Averaging these inequalities against the seed distribution bounds the expected query count by the expectation of the constant $n$. The seed probabilities sum to one, so that last expectation equals $n$.

**Key facts.** `FABL.FiniteDecisionTree.queryCount_le_dimension`.
