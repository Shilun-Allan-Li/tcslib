<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.transProb_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Transition Probabilities

**Claim.** For every number of steps and every pair of vertices, the transition probability from the first vertex to the second is nonnegative.

**Proof.** By definition, the transition probability is the number of index sequences that lead from the starting vertex to the destination, divided by $D^k$. The numerator is a nonnegative integer, and the denominator is a nonnegative rational power of the natural number $D$. Hence the quotient is nonnegative.
