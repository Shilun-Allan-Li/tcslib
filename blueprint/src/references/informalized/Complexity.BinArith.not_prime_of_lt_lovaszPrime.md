<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.not_prime_of_lt_lovaszPrime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primes below the Lovász prime

**Claim.** If $2^{\lceil\log_2(2n)\rceil}<q$ and $q$ is less than the Lovász prime, then $q$ is not prime.

**Proof.** By definition, the Lovász prime is the least prime strictly greater than $2^{\lceil\log_2(2n)\rceil}+1$. If $q$ were prime, the assumed lower bound would make it strictly greater than that threshold, so it would be a qualifying prime. The least such prime cannot exceed any qualifying prime, contradicting that $q$ is smaller than the Lovász prime.
