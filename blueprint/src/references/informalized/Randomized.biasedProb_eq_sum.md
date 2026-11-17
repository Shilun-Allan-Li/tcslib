<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.biasedProb_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Sum Formula for Biased Probability

**Claim.** The biased probability of a decidable event on length-$m$ Boolean words is the sum over all length-$m$ Boolean vectors of the event indicator times the product of the individual bit probabilities, with a true bit weighted by $\rho$ and a false bit by $1-\rho$.

**Proof.** Induct on $m$, allowing the event to vary. For $m=0$, there is just the empty vector, and its empty product is $1$; the sum is therefore $1$ or $0$ according as the event holds or fails on the empty word, matching the definition of biased probability. For the successor step, split the probability according to the first bit using the recurrence (`Randomized.biasedProb_succ`), then apply the induction hypothesis to the two resulting events on the remaining $m$ bits. Re-index the sum over vectors of length $m+1$ as a sum over the first Boolean coordinate and the remaining vector. Distributing the two branch weights through these sums gives exactly the product formula: the first coordinate contributes $\rho$ when true and $1-\rho$ when false, while the remaining coordinates contribute their respective factors from the induction hypothesis. In each branch the event indicator selects precisely those vectors whose associated word satisfies the event.

**Key facts.** `Randomized.biasedProb_succ`.
