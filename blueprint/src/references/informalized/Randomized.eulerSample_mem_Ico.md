<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PrimalityMath.lean :: Randomized.eulerSample_mem_Ico -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of the Euler sample

**Claim.** If $N>1$, then for every finite binary string $r$, the Euler sample obtained from $N$ and $r$ lies in $[1,N)$.

**Proof.** The sample is $1+(\operatorname{bitsVal}(r)\bmod(N-1))$. Since $N>1$, the modulus $N-1$ is positive, so the remainder is between $0$ and $N-2$. Adding one places the sample between $1$ and $N-1$, inclusive, which is precisely membership in $[1,N)$.
