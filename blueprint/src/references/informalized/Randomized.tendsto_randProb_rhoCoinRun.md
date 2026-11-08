<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.tendsto_randProb_rhoCoinRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Limit of the matching-run probability

**Claim.** For a Boolean sequence $p$, the probability that a uniformly chosen length-$K$ word makes the matching-run procedure return true converges to the binary-value sum of $p$.

**Proof.** The probability is bounded above by the binary-value sum, and the binary-value sum is at most that probability plus $2^{-K}$, by the two bounds `randProb_rhoCoinRun_le_binVal` and `binVal_le_randProb_rhoCoinRun_add`. The error term $2^{-K}$ tends to zero, so the probability lies between the binary-value sum minus $2^{-K}$ and the constant binary-value sum. Both bounds converge to that sum. The squeeze theorem gives the claimed convergence.

**Key facts.** `Randomized.binVal_le_randProb_rhoCoinRun_add`, `Randomized.randProb_rhoCoinRun_le_binVal`.
