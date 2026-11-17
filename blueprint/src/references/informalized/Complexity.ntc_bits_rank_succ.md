<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean :: Complexity.ntc_bits_rank_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Expansion of the Successor Rank

**Claim.** For every finite bit string $s$, the binary expansion of one more than its rank is exactly $s$ followed by $1$.

**Proof.** By the preceding encoding identity (`ntc_bits_codeBitsNat_append_true`), the binary expansion of the number encoded by $s$ followed by $1$ is that same bit string. This encoded number is positive: if it were zero, its binary expansion would be empty, contradicting the displayed expansion ending in $1$. The rank is this positive number minus one, so adding one to the rank recovers the encoded number by cancellation of natural-number subtraction. Its binary expansion is therefore $s$ followed by $1$.

**Key facts.** `Complexity.ntc_bits_codeBitsNat_append_true`.
