<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.biasedProb_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of the Certain Event

**Claim.** For any real bias parameter $\rho$ and nonnegative integer $m$, the biased probability of the predicate that is always true is $1$.

**Proof.** Induct on $m$. At length zero the empty string satisfies the predicate, so its probability is one. At the inductive step, both first-bit branches are again the certain event and each has probability one by induction. The recursion (`Randomized.biasedProb_succ`) therefore gives $\rho\cdot1+(1-\rho)\cdot1=1$.

**Key facts.** `Randomized.biasedProb_succ`.
