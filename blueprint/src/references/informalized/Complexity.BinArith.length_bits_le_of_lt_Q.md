<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.length_bits_le_of_lt_Q -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Length Under an Exponential Bound

**Claim.** If $p<2^K$ and $x<p+2^K+2$, then the binary expansion of $x$ has length at most $K+2$.

**Proof.** Since $p<2^K$, the assumed bound gives $x<2^{K+1}+2$. Also $2^K\ge1$, so $2^{K+1}+2\le 2^{K+2}$. Hence $x<2^{K+2}$, and the standard bound that a number below $2^m$ has binary expansion length at most $m$ (`length_bits_le`) with $m=K+2$ proves the result.

**Key facts.** `Complexity.LogProg.length_bits_le`.
