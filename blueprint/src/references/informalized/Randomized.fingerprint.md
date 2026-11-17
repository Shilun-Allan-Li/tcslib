<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.fingerprint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondivisibility fingerprint probability

**Claim.** For $M\ge12$ and nonzero $y$ with $|y|\le 2^{5M2^M}$, a uniformly chosen Boolean string of length $2M$, interpreted as its binary value $v$, has probability at least $1/(4M)$ that $v+1$ does not divide $y$.

**Proof.** The binary-value map sends the uniformly chosen strings of length $2M$ uniformly over the integers in $[0,2^{2M})$. Thus the probability in question is the number $c$ of integers $v$ in that range for which $v+1$ does not divide $y$, divided by $2^{2M}$ (`randProb_bitsVal`). Prime counting supplies a lower bound on this count: the number of primes below $2^{2M}$ is at most $c+5M2^M$, using the bound on $|y|$ (`primeCounting_le_card_not_dvd`). On the other hand, the prime-counting estimate gives $2^{2M}\le 2M(\pi(2^{2M})+1)$ (`two_pow_le_mul_primeCounting`). Combining these inequalities yields $2^{2M}\le 2M(c+5M2^M+1)$. The exponential inequality $4M(1+5M2^M)\le 2^{2M}$ (`four_mul_le_four_pow`) then implies $2^{2M}\le4Mc$. Dividing by $4M2^{2M}$ gives the asserted probability bound.

**Key facts.** `Randomized.randProb_bitsVal`, `Randomized.two_pow_le_mul_primeCounting`, `Randomized.primeCounting_le_card_not_dvd`, `Randomized.four_mul_le_four_pow`.
