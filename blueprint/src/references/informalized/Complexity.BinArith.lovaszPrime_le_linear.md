<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.lovaszPrime_le_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear bound for the chosen prime

**Claim.** For every natural number $n$, the least prime strictly greater than $2^{\lceil\log_2(2n)\rceil}$ is at most $8n+2$.

**Proof.** The chosen prime is at most $2^{\lceil\log_2(2n)\rceil+1}$, by the upper bound for the chosen prime (`lovaszPrime_le`). Rewriting this as twice $2^{\lceil\log_2(2n)\rceil}$ and using $2^{\lceil\log_2(2n)\rceil}\le 4n+1$ (`two_pow_clog_le`) gives an upper bound of $2(4n+1)=8n+2$.

**Key facts.** `Complexity.BinArith.lovaszPrime_le`, `Complexity.BinArith.two_pow_clog_le`.
