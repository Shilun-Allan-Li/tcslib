<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.two_pow_card_primeFactors_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prime factors bounded by the integer

**Claim.** For each nonzero natural number $k$, the number of distinct prime divisors of $k$ satisfies $2^{\#\{p:p\text{ prime and }p\mid k\}}\le k$.

**Proof.** Write $2^{\#k.\mathrm{primeFactors}}$ as a product of one factor $2$ for each distinct prime divisor of $k$. Each such prime is at least $2$, so this product is at most the product of those prime divisors. The product of the distinct prime divisors divides $k$, and since $k>0$, any positive divisor of $k$ is at most $k$. Combining these inequalities proves the claim.
