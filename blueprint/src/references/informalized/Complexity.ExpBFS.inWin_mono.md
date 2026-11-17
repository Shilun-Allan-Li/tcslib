<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.inWin_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Work-Tape Windows

**Claim.** If a configuration lies within the window of radius $s$, then it lies within every larger window of radius $s'\ge s$.

**Proof.** Each head’s distance from the origin is at most $s$, hence at most $s'$. If a cell lies outside the larger window, it also lies outside the original window, so its contents are blank by the original hypothesis. These two observations give the head and blank-cell conditions for radius $s'$.
