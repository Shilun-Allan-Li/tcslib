<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.uniformExcess_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative uniform excess

**Claim.** If $V$ is finite and nonempty and $p:V\to\mathbb Q$ has sum $1$, then its uniform excess, the maximum of $p(v)-1/|V|$, is nonnegative.

**Proof.** Let $n=|V|$, which is positive because $V$ is nonempty. The deviations $p(v)-1/n$ sum to zero (`Randomized.sum_sub_inv_card`). Each is bounded above by their maximum, the uniform excess (`Randomized.le_uniformExcess`), so their sum is at most $n$ times that maximum. Since the sum is zero and $n>0$, the maximum must be nonnegative.

**Key facts.** `Randomized.sum_sub_inv_card`, `Randomized.le_uniformExcess`.
