<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.le_two_pow_size_pred -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds from Binary Size

**Claim.** For $N\ge 1$, the power $2^{\operatorname{size}(N-1)}$ is at least $N$ and strictly less than $2N$.

**Proof.** The defining size bound gives $N-1<2^{\operatorname{size}(N-1)}$, which implies $N\le 2^{\operatorname{size}(N-1)}$. For the upper bound, first consider size zero. Then the power is $1$, and the assumed positivity of $N$ gives $1<2N$. If the size is positive, the characterization of size yields $2^{\operatorname{size}(N-1)-1}\le N-1$. The power with exponent equal to the size is twice this lower power, so it is at most $2(N-1)$, which is strictly less than $2N$.
