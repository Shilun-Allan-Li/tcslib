<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Decode_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding State Length Bound

**Claim.** For every binary word $w$ and natural number $j$, the state for $w$ at count $j$ has length at most $2|w|+3j+4$.

**Proof.** A pair encoding of lists $a,b$ has length $2|a|+|b|+2$: each bit of $a$ is duplicated, a two-bit delimiter is added, and then $b$ is appended. Apply this formula to the outer and inner encodings in the state. The unary counter has length $j$, while the final field has length either $\mathrm{clNum}(w)$ when $\mathrm{clNum}(w)\le j$, or zero otherwise. In the first case its length is at most $j$, and in the second it is zero. Substituting these bounds into the pair-encoding length formula gives the claimed bound.
