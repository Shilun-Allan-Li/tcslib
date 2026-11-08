<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: BoolCircuit.three_pow_log_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A power of three bounded by a square

**Claim.** For every nonnegative integer $n$, $3^{\log_2 n}\le(n+1)^2$, where $\log_2 n$ is the integer logarithm.

**Proof.** The integer-logarithm bound gives $2^{\log_2 n}\le n$ when $n>0$, hence certainly $2^{\log_2 n}\le n+1$; for $n=0$ the latter inequality holds directly. Since $3\le4$, raising both sides to the exponent $\log_2 n$ gives $3^{\log_2 n}\le4^{\log_2 n}$. The right-hand side is $(2^{\log_2 n})^2$, which is at most $(n+1)^2$ because squaring preserves order on nonnegative integers. Combining these inequalities proves the claim.
