<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.vonNeumann_tails -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of Returning False

**Claim.** For any real number $\rho$ and natural number $K$, the probability that the rule returns false after examining $2K$ independent bits is $\frac{1-(\rho^2+(1-\rho)^2)^K}{2}$.

**Proof.** Proceed by induction on $K$. For $K=0$, no bit is returned, so the probability of returning false is zero, as is the claimed expression. For the inductive step, expand according to the first pair using the two-bit probability formula (`Randomized.biasedProb_two`). An equal pair contributes the probability for the remaining bits, while an unequal pair contributes according to its first bit: the pair true-then-false returns true and contributes zero; false-then-true returns false and contributes its full pair weight. Applying the induction hypothesis to the equal-pair continuations, and using that the continuation probabilities for an always-false or always-true event are zero or one, respectively (`Randomized.biasedProb_false`, `Randomized.biasedProb_true`), the resulting expression simplifies to $\frac{1-(\rho^2+(1-\rho)^2)^{K+1}}{2}$.

**Key facts.** `Randomized.biasedProb_two`, `Randomized.biasedProb_false`, `Randomized.biasedProb_true`.
