<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.two_pow_lovaszBits_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict Power Bound for the Lovász Bit Count

**Claim.** For every nonzero natural number $n$, if $L=\lceil\log_2(2n)\rceil$ in the natural-number ceiling convention, then $2^L<4n$.

**Proof.** Since $n$ is nonzero, $2n>1$, and hence $L=\operatorname{clog}_2(2n)$ is positive. The predecessor ceiling-logarithm bound gives $2^{L-1}<2n$. Express the positive natural number $L$ as $j+1$; then the bound reads $2^j<2n$. Multiplying by $2$ gives $2^L<4n$, as required.
