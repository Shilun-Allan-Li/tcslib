<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCounts_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Movement Counts Bounded by Time

**Claim.** Every coordinate of the movement-count vector at time $t$ is at most $t$.

**Proof.** Induct on $t$. At time zero every count is zero, so each is at most zero. For the successor step, the count vector is obtained by advancing the previous vector once. The one-step bound (`Complexity.clAdvance_bound`) says that if every previous coordinate is at most $t$, then every coordinate after this advance is at most $t+1$. The induction hypothesis supplies its premise.

**Key facts.** `Complexity.clAdvance_bound`.
