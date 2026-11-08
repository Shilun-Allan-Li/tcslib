<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.lt_two_pow_size_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Size Power Bound

**Claim.** Every natural number $n$ is strictly less than $2^{\operatorname{size}(n)+1}$.

**Proof.** The standard binary-size bound gives $n<2^{\operatorname{size}(n)}$. Since $2>1$, increasing the exponent from $\operatorname{size}(n)$ to $\operatorname{size}(n)+1$ strictly increases the power. Therefore $n<2^{\operatorname{size}(n)+1}$.
