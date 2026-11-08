<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.lovaszPrime_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound for the chosen prime

**Claim.** For every natural number $n$, the least prime strictly greater than $2^{\lceil\log_2(2n)\rceil}$ is at most $2^{\lceil\log_2(2n)\rceil+1}$.

**Proof.** Apply the prime existence bound that, for a positive natural number $m$, there is a prime $p$ with $m<p\le 2m$. Take $m=2^{\lceil\log_2(2n)\rceil}$, which is positive. This gives a prime above the defining threshold and no greater than twice that threshold. Since the chosen number is the least prime above the threshold, it is at most $p$, and therefore at most $2m=2^{\lceil\log_2(2n)\rceil+1}$.
