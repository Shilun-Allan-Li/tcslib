<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.biasedProb_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Biased Probability of a Complement

**Claim.** For every real bias parameter $\rho$, nonnegative integer $m$, and predicate $A$, the biased probability that $A$ fails is one minus the biased probability of $A$.

**Proof.** Induct on $m$, allowing $A$ to vary. At length zero, split according to whether $A$ holds of the empty string: exactly one of $A$ and its complement holds there, so their probabilities sum to one. For the inductive step, expand the probability of the complement and the probability of $A$ into their true and false first-bit branches (`Randomized.biasedProb_succ`). Apply the induction hypothesis to each branch. The resulting expression simplifies to one minus the original probability, using that the two branch weights are $\rho$ and $1-\rho$.

**Key facts.** `Randomized.biasedProb_succ`.
