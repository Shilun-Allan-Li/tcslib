<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.mul_succ_pow_le_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Polynomial Factor Bounded by a Power

**Claim.** For natural numbers $m,k,n$ with $2\le n$, one has $(m+1)(n+1)^{2k}\le n^{m+1+4k}$.

**Proof.** First, $n+1\le n^2$ for $n\ge2$. Raising both sides to $2k$ gives $(n+1)^{2k}\le (n^2)^{2k}=n^{4k}$. Also, the elementary power bound $r\le n^r$ for $n\ge2$ gives $m+1\le n^{m+1}$. Multiplying these two inequalities yields $(m+1)(n+1)^{2k}\le n^{m+1}n^{4k}$. Combining powers gives the desired bound.

**Key facts.** `Complexity.le_pow_self_of_two_le`.
