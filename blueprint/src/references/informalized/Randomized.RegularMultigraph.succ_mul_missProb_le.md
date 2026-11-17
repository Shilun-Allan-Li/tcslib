<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.succ_mul_missProb_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Miss Probability and Cumulative Miss Probability

**Claim.** For every $L$, $(L+1)$ times the probability of missing $t$ in a uniformly chosen length-$L$ sequence of neighbor indices from $s$ is at most the sum of miss probabilities at times $0$ through $L$.

**Proof.** Miss probability is nonincreasing with the number of steps (`missProb_antitone`). Thus for every $j$ from $0$ to $L$, the miss probability at time $j$ is at least the miss probability at time $L$. The sum over these $L+1$ indices is therefore at least $(L+1)$ copies of the time-$L$ miss probability, which is the asserted inequality.

**Key facts.** `Randomized.RegularMultigraph.missProb_antitone`.
