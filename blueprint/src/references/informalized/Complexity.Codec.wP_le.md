<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean :: Complexity.Codec.wP_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary width bound

**Claim.** For every natural number $n$, the length of the binary expansion of $n+1$ is at most $n+1$.

**Proof.** The length of the binary expansion of a natural number is at most its base-two logarithm plus one (`length_bits_le_log`). Also, for every positive integer $m$, its base-two logarithm is strictly less than $m$ (`Nat.log_lt_self`); apply this with $m=n+1$, which is positive. Combining these inequalities gives $(	ext{Nat.bits}(n+1)).	ext{length}\le n+1$, as required.

**Key facts.** `Complexity.LogProg.length_bits_le_log`.
