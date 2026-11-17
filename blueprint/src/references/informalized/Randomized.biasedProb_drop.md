<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.biasedProb_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dropping a Prefix Preserves Biased Probability

**Claim.** The biased probability that a length-$(s+n)$ sampled word satisfies $P$ after its first $s$ bits are dropped equals the biased probability that a length-$n$ sampled word satisfies $P$.

**Proof.** Induct on the prefix length $s$, with $n$ and $P$ arbitrary. When $s=0$, dropping the empty prefix leaves the word unchanged. For the successor step, rewrite the total length as $(s+n)+1$ and split according to the first sampled bit using the one-step recurrence (`Randomized.biasedProb_succ`). After either bit is prefixed, dropping the first $s+1$ bits is the same as dropping the next $s$ bits from the remaining word. Apply the induction hypothesis to each branch; both branch probabilities reduce to the same length-$n$ probability. Their recurrence weights add to $\rho+(1-\rho)=1$, yielding the result.

**Key facts.** `Randomized.biasedProb_succ`.
