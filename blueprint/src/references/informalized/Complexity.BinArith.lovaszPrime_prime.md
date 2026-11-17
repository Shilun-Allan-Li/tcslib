<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/PrimeFind.lean :: Complexity.BinArith.lovaszPrime_prime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primality of the chosen number

**Claim.** For every natural number $n$, the number chosen as the least prime strictly greater than $2^{\lceil\log_2(2n)\rceil}$ is prime.

**Proof.** The defining existence statement for the chosen number supplies a number that is prime and strictly greater than the threshold. The chosen number is obtained as the least number satisfying that property, so it also satisfies the property; in particular it is prime.
