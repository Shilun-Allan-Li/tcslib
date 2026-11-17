<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.freshLen_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Properties of the chosen length

**Claim.** The length chosen for $i$ and $b$ satisfies $b<m$, $i+2\le m$, and $m^i+i<2^m$.

**Proof.** By definition, $m$ is chosen from the numbers whose existence is asserted by the fresh-length existence theorem (`Complexity.exists_fresh_len`). The specification of that chosen witness is precisely the conjunction of the three stated inequalities.

**Key facts.** `Complexity.exists_fresh_len`.
