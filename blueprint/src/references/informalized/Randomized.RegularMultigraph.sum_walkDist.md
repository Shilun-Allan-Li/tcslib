<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.sum_walkDist -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conservation of Walk Distribution Mass

**Claim.** For any rational-valued function on the vertices, the sum over destinations of its walk distribution after any number of steps equals the original sum of the function.

**Proof.** Expand the walk distribution as the sum over starting vertices of the initial weight times the transition probability. Interchange the finite sums to group terms by starting vertex. For each such vertex, factor out its initial weight; the remaining sum over destinations is $1$ by the total transition probability identity (`Randomized.RegularMultigraph.sum_transProb_right`). The resulting sum is exactly the sum of the initial function over vertices.

**Key facts.** `Randomized.RegularMultigraph.sum_transProb_right`.
