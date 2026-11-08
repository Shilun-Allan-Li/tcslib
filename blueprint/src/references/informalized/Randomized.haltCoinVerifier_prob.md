<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.haltCoinVerifier_prob -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting-Coin Verifier Success Probability

**Claim.** For every finite bit string $x$, a random bit string of length $32(|x|+1)^2$, with independent bits equal to $1$ with probability the halting coin, makes the verifier output the correct membership indicator with probability at least $2/3$.

**Proof.** Let $k=32(|x|+1)^2$ and $d=d(x)$. The halting coin lies in $[0,1]$ (`Randomized.haltCoin_mem`), so the concentration bound for the number of ones in a biased random string applies. It bounds the probability that the empirical fraction of ones differs from the coin by more than $\delta=1/(4d)$ by $2\exp(-2\delta^2k)$. Since $d\le |x|+1$ (`Randomized.hlD_le`), the exponent satisfies $-2\delta^2k\le-4$. Also $\exp(4)\ge6$, so the bad-event probability is at most $2\exp(-4)\le1/3$. Consequently the event that the empirical fraction is within $1/(4d)$ has probability at least $2/3$. The verifier agrees with the membership indicator on this event by `Randomized.haltCoinVerifier_eq`; the monotonicity of biased probability transfers the lower bound to the event of correct output (`Randomized.biasedProb_mono`).

**Key facts.** `Randomized.haltCoin_mem`, `Randomized.hlD_le`, `Randomized.biasedProb_count_dev_le`, `Randomized.biasedProb_not`, `Randomized.haltCoinVerifier_eq`, `Randomized.biasedProb_mono`.
