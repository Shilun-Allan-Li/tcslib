<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.two_pow_lt_lovaszPrime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Least-prime power bound

**Claim.** For every natural number $n$, the least prime $p_n$ at least $2^{\lceil\log_2(2n)\rceil}+1$ is strictly greater than $2^{\lceil\log_2(2n)\rceil}$.

**Proof.** By the defining property of the least prime, the chosen prime is at least the threshold $2^{\lceil\log_2(2n)\rceil}+1$. Since these are natural numbers, being at least that threshold makes it strictly greater than $2^{\lceil\log_2(2n)\rceil}$.
