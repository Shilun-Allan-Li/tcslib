<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.mv_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter Transfer in the Search Machine

**Claim.** The counter-transfer phase reaches the counter-copy phase, setting $c$ to zero and $c_1$ to its former value plus $c$, while preserving memory and head position. Every earlier configuration satisfies the register bounds, head-position bounds, and instruction side conditions.

**Proof.** Apply the register-machine transfer lemma `move_run` to the two distinct counters $c$ and $c_1$. Its loop repeatedly tests whether $c$ is zero; while it is nonzero, it decrements $c$ and increments $c_1$, and then returns to the test. Thus after exactly the original value of $c$ iterations, $c=0$ and $c_1$ has increased by that amount. The hypotheses that every starting register is at most $B$ and that $c_1+c\le B$ ensure the register bound throughout the loop. The guard also records the required instruction side conditions. Converting the resulting register run to the memory-machine run with `of_areach` preserves the memory and head position; the assumed bounds on the initial head position therefore continue to hold throughout.

**Key facts.** `Complexity.LogProg.move_run`, `Complexity.LogProg.ExpBFS.of_areach`.
