<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.two_pow_clog_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for a Power of Two

**Claim.** For every natural number $n$, $2^{\lceil\log_2(2n)\rceil}\le 4n+1$, with the natural-number ceiling convention.

**Proof.** If $n=0$, the claimed inequality follows directly. Otherwise $2n>1$, so the ceiling logarithm $L=\operatorname{clog}_2(2n)$ is positive. The predecessor ceiling-logarithm bound gives $2^{L-1}<2n$. Write $L=j+1$, so this says $2^j<2n$. Multiplying by $2$ yields $2^L<4n$, which implies the stated, slightly weaker, bound $2^L\le 4n+1$.
