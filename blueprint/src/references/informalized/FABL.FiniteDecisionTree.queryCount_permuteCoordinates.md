<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeSymmetrization.lean :: FABL.FiniteDecisionTree.queryCount_permuteCoordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query Count Under Coordinate Permutations

**Claim.** Permuting the coordinates of a finite decision tree and running it on $x$ gives the same query count as running the original tree on the input $i\mapsto x(\sigma(i))$.

**Proof.** The query-trace transformation says that the permuted tree's trace on $x$ is obtained by applying $\sigma$ to each coordinate in the original tree's trace on the input $i\mapsto x(\sigma(i))$ (`queryTrace_permuteCoordinates`). Applying a coordinate map to each list entry preserves the list's length. Since query count is the length of the trace, the two query counts are equal.

**Key facts.** `FABL.FiniteDecisionTree.queryTrace_permuteCoordinates`.
