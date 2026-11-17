<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.randProb_rhoCoinRun_le_binVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Coin-Run Probability Bound

**Claim.** For any Boolean sequence $p$ and $K\ge0$, the probability that a uniformly chosen length-$K$ word first differs at a position where $p$ is true is at most the binary value of $p$.

**Proof.** By the real-valued finite coin-run formula (`Randomized.randProb_rhoCoinRun_eq_sum_real`), the probability is the sum of the first $K$ terms in the series defining the binary value. Summability (`Randomized.summable_binVal`) lets us decompose that value into this finite partial sum plus the tail. Every term of the tail is nonnegative, so the partial sum is at most the full sum.

**Key facts.** `Randomized.randProb_rhoCoinRun_eq_sum_real`, `Randomized.summable_binVal`.
