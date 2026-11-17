<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.logSpace_le_size_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic Space Bound

**Claim.** For every natural number $n$, the logarithmic space measure $\log_2 n+1$ is at most the binary size of $n$ plus one.

**Proof.** Unfold the logarithmic space measure and split into $n=0$ and $n>0$. At zero, the inequality follows directly from the definitions. For positive $n$, the defining property of the base-two logarithm gives $2^{\log_2 n}\le n$, while the binary-size bound gives $n<2^{\operatorname{size}(n)}$. Hence $2^{\log_2 n}<2^{\operatorname{size}(n)}$. Since exponentiation with base $2>1$ is strictly increasing in the exponent, $\log_2 n<\operatorname{size}(n)$. Adding one to both sides yields the desired inequality.
