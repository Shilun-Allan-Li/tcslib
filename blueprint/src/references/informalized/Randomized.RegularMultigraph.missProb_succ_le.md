<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.missProb_succ_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Decrease in Miss Probability

**Claim.** For every $k$, the miss probability from $s$ after $k+1$ steps is at most the miss probability from $s$ after $k$ steps.

**Proof.** Induct on $k$, proving the inequality for every starting vertex. If $s=t$, both miss probabilities are zero (`missProb_self`). For the base case away from the target, the recurrence identifies the one-step miss probability with the average of the zero-step miss probabilities at the neighbors. Each such probability is at most $1$, by the upper bound on miss probability (`missProb_mem_Icc`), so the average is at most the constant average $1$ (`avg_mono`, `avg_const`). The zero-step miss probability at $s\ne t$ is $1$ (`missProb_zero_of_ne`). For the induction step away from the target, apply the recurrence to both lengths: the desired comparison follows by averaging the induction hypothesis over neighbors (`avg_mono`).

**Key facts.** `Randomized.RegularMultigraph.missProb_self`, `Randomized.RegularMultigraph.missProb_succ`, `Randomized.RegularMultigraph.missProb_mem_Icc`, `Randomized.RegularMultigraph.avg_mono`, `Randomized.RegularMultigraph.avg_const`, `Randomized.RegularMultigraph.missProb_zero_of_ne`.
