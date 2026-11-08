<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.vonNeumann_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of No Output

**Claim.** For any real number $\rho$ and natural number $K$, the probability that the rule returns no bit after examining $2K$ independent bits is $(\rho^2+(1-\rho)^2)^K$.

**Proof.** Proceed by induction on $K$. With no bits, the rule returns no bit, so the probability is $1$, matching the zeroth power. For the inductive step, condition on the first two bits using the two-bit expansion of the biased probability (`Randomized.biasedProb_two`). If they are unequal, the rule returns a bit, so this event contributes zero. If they are both true or both false, the rule continues on the remaining $2K$ bits; each equal pair has probability weight $\rho^2$ or $(1-\rho)^2$, respectively. By the induction hypothesis, the remaining probability of no output is $(\rho^2+(1-\rho)^2)^K$. Adding the two equal-pair contributions gives $(\rho^2+(1-\rho)^2)(\rho^2+(1-\rho)^2)^K$, which is the claimed $(K+1)$st power.

**Key facts.** `Randomized.biasedProb_two`, `Randomized.biasedProb_false`.
