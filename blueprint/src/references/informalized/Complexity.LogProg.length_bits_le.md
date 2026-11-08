<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.length_bits_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for Binary Expansion

**Claim.** If natural numbers $n$ and $m$ satisfy $n<2^m$, then the binary expansion of $n$ has length at most $m$.

**Proof.** The length of the binary expansion equals the binary size of the number (`Nat.size_eq_bits_len`). The size bound theorem says that if $n<2^m$, then the size of $n$ is at most $m$ (`Nat.size_le`). Combining these gives the result.
