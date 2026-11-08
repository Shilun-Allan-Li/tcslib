<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.vonNeumann_heads -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of returning true

**Claim.** For any real $\rho$ and natural number $K$, the probability that the pair rule returns true on $2K$ independent bits is $\bigl(1-(\rho^2+(1-\rho)^2)^K\bigr)/2$.

**Proof.** Proceed by induction on $K$. For $K=0$, there are no pairs, so the rule cannot return true, and the formula is zero. For the induction step, split according to the first pair. The equal outcomes (true-true and false-false) leave the same rule to run on the remaining $2K$ bits; the unequal outcomes return their first bit immediately. Expanding these four cases with the two-bit probability recurrence (`Randomized.biasedProb_two`), the constant-event probabilities (`Randomized.biasedProb_false`, `Randomized.biasedProb_true`), and the induction hypothesis gives the stated expression for $K+1$ after collecting terms.

**Key facts.** `Randomized.biasedProb_two`, `Randomized.biasedProb_false`, `Randomized.biasedProb_true`.
