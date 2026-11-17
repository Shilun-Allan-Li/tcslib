<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.expTimeLe_rhoCoinRun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected runtime of the mismatch procedure

**Claim.** For every infinite Boolean sequence $p$, the sum over $s<K$ of the probabilities that the mismatch procedure has not halted after $s$ bits is at most $2$.

**Proof.** At time $K$, the procedure has not halted exactly when the first $K$ random bits agree with the first $K$ terms of $p$. Each bit is uniform, so this event has probability $2^{-K}$; equivalently, its probability is $(1/2)^K$ (`Randomized.notHaltedProb_rhoCoinRun`). Thus the sum through the cutoff is the finite geometric sum $\sum_{s<K}(1/2)^s$, which is at most $2$ because the ratio $1/2$ lies between zero and one.

**Key facts.** `Randomized.notHaltedProb_rhoCoinRun`.
