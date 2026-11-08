<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.lt_of_uniformSample_eq_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of a Uniform Sample

**Claim.** For natural numbers $N,k$, a bit string $r$, and a natural number $i$, if the sampling procedure with parameters $N,k$ and input $r$ returns $i$, then $i<N$.

**Proof.** Rewrite the sampling procedure as a search through the finite list of candidate block values: it returns the first value in that list satisfying the condition of being less than $N$ (`Randomized.sampleTries_eq_find`). Since the search returned `some i`, the defining property of a successful list search gives that the returned element satisfies the predicate. Therefore $i<N$.

**Key facts.** `Randomized.sampleTries_eq_find`.
