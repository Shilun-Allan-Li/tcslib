<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_inc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Counter Increment

**Claim.** Under the stated head-position and length bounds, the incrementing configuration reaches the read-phase configuration with the selected tape storing the binary representation of $n+1$ and its head back at $0$, while the other configuration data are retained.

**Proof.** The binary increment procedure has a finite run from the configuration with tape $r$ storing $n$ to the one storing $n+1$ (`Complexity.LogProg.inc_run`). It also bounds the head position throughout that run between $-1$ and the bit-length of $n+1$. The hypothesis $n+1\le |y|+1$, together with monotonicity of binary bit-length (`Complexity.LogProg.length_bits_mono`), puts this upper bound within the global safety bound for the input. Thus each configuration along the run remains safe: the other tapes and heads retain their values, and the changing tape's head satisfies the required bounds (`Complexity.LogProg.access_frame`). The safe finite run gives the asserted access path (`Complexity.LogProg.accessPath_of_run`).

**Key facts.** `Complexity.LogProg.inc_run`, `Complexity.LogProg.length_bits_mono`, `Complexity.LogProg.access_frame`, `Complexity.LogProg.accessPath_of_run`.
