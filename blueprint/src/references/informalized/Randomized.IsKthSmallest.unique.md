<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Median.lean :: Randomized.IsKthSmallest.unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness at a Fixed Rank

**Claim.** Two elements of a linearly ordered list that both satisfy the stated rank condition for the same $k$ must be equal.

**Proof.** First show that if $y$ and $z$ both satisfy the rank condition, then $y$ cannot be strictly less than $z$. If $y<z$, every entry at most $y$ is strictly below $z$. Thus the number of entries at most $y$ is at most the number strictly below $z$, by monotonicity of list counts under predicate implication. But the rank conditions say that the first number is at least $k$ while the second is less than $k$, a contradiction. Now apply trichotomy: $y<z$ is impossible by this argument, and $z<y$ is impossible by the same argument with the roles reversed. Therefore $y=z$.
