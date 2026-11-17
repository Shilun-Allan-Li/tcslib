<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.randProb_rhoCoinRun_eq_sum_real -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real-Valued Finite Coin-Run Probability

**Claim.** For a Boolean sequence $p$ and $K\ge0$, the probability that a uniformly chosen length-$K$ word first differs from $p$ at a true bit, viewed as a real number, equals $\displaystyle\sum_{i=0}^{K-1}\frac{\mathbf 1_{\{p_i=\mathrm{true}\}}}{2^{i+1}}$.

**Proof.** Use the rational-valued finite coin-run formula (`Randomized.randProb_rhoCoinRun_eq_sum`) and cast both sides to the reals. Casting commutes with the finite sums, powers, and divisions involved. For each index, the cast of the indicator is the corresponding real indicator, so the resulting expression is exactly the stated real sum.

**Key facts.** `Randomized.randProb_rhoCoinRun_eq_sum`.
