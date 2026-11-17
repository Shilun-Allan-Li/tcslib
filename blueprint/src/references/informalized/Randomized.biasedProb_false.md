<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.biasedProb_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of the Empty Event

**Claim.** For every real bias parameter and every nonnegative integer $m$, the biased probability of the event that is always false is zero.

**Proof.** Induct on $m$. At $m=0$, the event fails on the empty word, so its probability is zero by the defining base case. For the successor, the one-step recurrence (`Randomized.biasedProb_succ`) expresses the probability as a weighted sum of the two branch probabilities. Each branch is again the event that is always false, so both vanish by the induction hypothesis, and the resulting sum is zero.

**Key facts.** `Randomized.biasedProb_succ`.
