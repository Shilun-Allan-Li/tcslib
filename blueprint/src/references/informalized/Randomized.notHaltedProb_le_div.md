<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.notHaltedProb_le_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive-Time Nonhalting Bound

**Claim.** If halting is prefix stable and the sum of nonhalting probabilities over every finite initial interval is at most $B$, then for every $t>0$ the nonhalting probability at time $t$ is at most $B/t$.

**Proof.** The prefix-stability and cumulative-bound hypotheses give the weighted estimate $t\,\mathrm{notHaltedProb}(r,t)\le B$ (`Randomized.mul_notHaltedProb_le`). Since $t>0$, division by $t$ preserves the inequality after dividing both sides by this positive number. This yields $\mathrm{notHaltedProb}(r,t)\le B/t$.

**Key facts.** `Randomized.mul_notHaltedProb_le`.
