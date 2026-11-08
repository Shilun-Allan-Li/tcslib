<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.randProb_rhoCoinRun_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Coin-Run Probability as a Sum

**Claim.** For a sequence of Boolean bits $p$ and $K\ge0$, the probability that a uniformly chosen length-$K$ word, scanned against $p$ in order, first differs at a position where $p_i$ is true is $\displaystyle\sum_{i=0}^{K-1}\frac{\mathbf 1_{\{p_i=\mathrm{true}\}}}{2^{i+1}}$.

**Proof.** Proceed by induction on the word length, allowing the bit sequence to vary in the induction hypothesis. At length zero, the scan cannot return a bit, so the event has probability zero, matching the empty sum. For length $K+1$, condition on the first word bit. If it matches $p_0$, the scan continues with the shifted sequence and a remaining word of length $K$; by the induction hypothesis, its contribution is the shifted finite sum, with the first-bit probability accounted for by a factor of $1/2$. If it differs from $p_0$, the scan immediately returns $p_0$: this branch contributes probability $1/2$ when $p_0$ is true and zero otherwise. The two branches have equal probability, as expressed by the one-bit decomposition of uniform probability (`Randomized.randProb_succ`). Combining the immediate contribution with half of the shifted sum gives the sum through index $K$, since each shifted denominator gains one factor of $2$. The empty-event and certain-event cases used for the two branches have probabilities zero and one, respectively (`Randomized.randProb_false`, `Randomized.randProb_true`); the event equivalences that reduce each branch to these cases or to the shifted scan preserve probability (`Randomized.randProb_congr`).

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_false`, `Randomized.randProb_true`, `Randomized.randProb_succ`.
