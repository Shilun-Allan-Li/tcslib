<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.hitTime_le_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Cumulative Miss Probability

**Claim.** For every $N$, the cumulative miss probability for hitting $t$ from $s$ through step $N-1$ is at most the corresponding cumulative miss probability through step $N$.

**Proof.** The sum through step $N$ is the sum through step $N-1$ together with the additional term $\operatorname{missProb}(t,N,s)$. This term is nonnegative, so adding it cannot decrease the sum.

**Key facts.** `Randomized.RegularMultigraph.missProb_mem_Icc`.
