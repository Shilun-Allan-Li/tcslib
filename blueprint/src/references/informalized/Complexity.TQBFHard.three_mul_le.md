<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean :: Complexity.TQBFHard.three_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound for a linear term

**Claim.** For every natural number $m$, one has $3m\le 2^{2m}$.

**Proof.** The elementary bound $m+1\le 2^m$ holds for every natural number. Also, $3m\le (m+1)^2$, since $(m+1)^2-3m=(m-1)^2+1$ is nonnegative. Squaring the first bound gives $(m+1)^2\le 2^m2^m=2^{2m}$. Combining these inequalities proves the claim.
