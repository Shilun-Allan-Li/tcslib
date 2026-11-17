<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.length_bits_pos_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary representation length bound

**Claim.** If $v\le n+1$, then the binary representation of $v$ has length at most that of $n+1$.

**Proof.** The length of the binary representation is monotone in its represented natural number (`length_bits_mono`). Applying this fact to $v\le n+1$ gives $(\mathrm{Nat.bits}\,v).\mathrm{length}\le (\mathrm{Nat.bits}\,(n+1)).\mathrm{length}$, which is the desired bound by the definition of $w_P(n)$.

**Key facts.** `Complexity.LogProg.length_bits_mono`.
