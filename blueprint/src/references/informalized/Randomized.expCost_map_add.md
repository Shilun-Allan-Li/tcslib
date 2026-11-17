<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.expCost_map_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected Cost Under an Additive Shift

**Claim.** If a probability mass function on pairs $(b,m)$ is transformed by replacing each pair with $(b,m+n)$, its expected second coordinate is the original expected second coordinate plus $n$.

**Proof.** View the map $(b,m)\mapsto(b,m+n)$ as sampling from the original distribution and then applying a deterministic distribution at each outcome. The expected cost of this bind is the sum of the original masses times the cost after the shift, by the expected-cost bind identity (`Randomized.expCost_bind`). A point mass at $(b,m+n)$ has cost $m+n$ (`Randomized.expCost_pure`). Splitting this as $m+n$ separates the original expected cost from $n$ times the total mass; the total mass of a probability mass function is one. The result follows.

**Key facts.** `Randomized.expCost_bind`, `Randomized.expCost_pure`.
