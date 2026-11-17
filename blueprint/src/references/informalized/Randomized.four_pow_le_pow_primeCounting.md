<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.four_pow_le_pow_primeCounting -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prime-Counting Exponential Bound

**Claim.** For every positive natural number $n$, $4^n\le (2n)^{\pi(2n)+1}$, where $\pi(x)$ counts the primes at most $x$.

**Proof.** First bound the central binomial coefficient $\binom{2n}{n}$. Its prime factorization expresses it as the product, over primes $p\le 2n$, of $p$ raised to the exponent of $p$ in the coefficient. Each such prime is at most $2n$, and the prime-power contribution $p^{v_p(\binom{2n}{n})}$ is at most $2n$. Thus the product is at most $(2n)^{\pi(2n)}$. The standard central-binomial lower bound gives $4^n\le 2n\binom{2n}{n}$ for $n>0$. Combining these inequalities yields $4^n\le 2n(2n)^{\pi(2n)}=(2n)^{\pi(2n)+1}$.
