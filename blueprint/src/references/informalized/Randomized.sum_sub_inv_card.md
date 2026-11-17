<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.sum_sub_inv_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered probabilities sum to zero

**Claim.** If $V$ is finite and nonempty and the rational-valued function $p$ has total sum $1$, then the sum over $V$ of $p(v)-1/|V|$ is zero.

**Proof.** Distribute the sum over the difference. The sum of the $p(v)$ terms is $1$ by hypothesis. The constant term contributes $|V|$ copies of $1/|V|$, whose sum is $1$ because $|V|$ is nonzero. Subtracting these two totals gives zero.
