<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.edgeExpectation_eq_neighborhoodExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Edge and neighborhood expectations agree

**Claim.** Averaging a function over uniformly chosen directed edges gives the same result as choosing a vertex uniformly and then a neighbor of that vertex uniformly.

**Proof.** Write both expectations as finite sums divided by the sizes of their respective sampling spaces. The directed-edge space is the dependent sum of vertices and their neighbors, so its cardinality is the sum of the neighborhood cardinalities. Regularity says each vertex has the same degree; consequently the edge count is the number of vertices times that degree. The iterated vertex-then-neighbor average has the same normalization and the same terms, because summing over the dependent sum is exactly summing first over vertices and then over their neighbors. The two expressions are therefore equal.
