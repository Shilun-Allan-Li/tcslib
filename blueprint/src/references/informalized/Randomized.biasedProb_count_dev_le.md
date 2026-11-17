<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.biasedProb_count_dev_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Bit-Count Deviation Bound

**Claim.** For $0\le p\le1$, positive $k$, and $\delta>0$, the probability that the fraction of true bits in a length-$k$ sample differs from $p$ by more than $\delta$ is at most $2\exp(-2\delta^2 k)$.

**Proof.** Identify the biased probability of the event with the real-valued probability, under the product measure of independent Bernoulli($p$) bits, that the corresponding Boolean word has the specified deviation (`Randomized.biasedProb_eq_toReal_iidBernoulli`). The iid Bernoulli average concentration bound (`Randomized.iid_bernoulli_avg_concentration`) bounds the measure of this event by the extended-real quantity $2\exp(-2\delta^2k)$. Its success count is the number of true entries in the associated word (`Randomized.successCount_eq_count`), so this is precisely the event in the claim. Taking real values preserves the inequality here; the right-hand side is finite and nonnegative, so its extended-real value converts back to the stated real bound.

**Key facts.** `Randomized.biasedProb_eq_toReal_iidBernoulli`, `Randomized.iid_bernoulli_avg_concentration`, `Randomized.successCount_eq_count`.
