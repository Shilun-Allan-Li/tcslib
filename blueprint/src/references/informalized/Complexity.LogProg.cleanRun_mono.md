<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMProof.lean :: Complexity.LogProg.cleanRun_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Clean Runs

**Claim.** If a machine has a clean run with head-position bound $B$, it has the same clean run with any larger bound $B'$.

**Proof.** Take the halting time and the terminal-state, output, blank-tape, and zero-head conditions witnessing the clean run at bound $B$. Keep the same time and terminal configuration. At every time up to that time, each head position has absolute value at most $B$, and $B\le B'$, so it also has absolute value at most $B'$. These data witness the clean run with the larger bound.
