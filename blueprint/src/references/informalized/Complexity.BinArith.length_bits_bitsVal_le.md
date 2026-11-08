<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.length_bits_bitsVal_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Binary Expansion Length

**Claim.** For every finite bit string $w$, the binary expansion of its represented value has length at most the length of $w$.

**Proof.** The represented value of a length-$m$ bit string is strictly less than $2^m$ (`bitsVal_lt_two_pow`). Any natural number strictly below $2^m$ has binary expansion length at most $m$ (`length_bits_le`). Taking $m$ to be the length of $w$ gives the result.

**Key facts.** `Complexity.LogProg.bitsVal_lt_two_pow`, `Complexity.LogProg.length_bits_le`.
