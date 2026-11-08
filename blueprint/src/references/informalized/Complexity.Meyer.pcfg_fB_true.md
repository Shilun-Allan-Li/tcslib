<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.pcfg_fB_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True Branch from the Second Field State

**Claim.** When the input symbol at position $p-1$ is true, one step from state $fB$ advances the input head to $p+1$ and enters $fA$ with flag $f$ and the same bit vector. It appends $b$ to $w_O$ when $f$ is true, or to $w_C$ when $f$ is false, and leaves $w_X$ unchanged.

**Proof.** The one-step formula for buffered configurations (`pcfg_step`) reduces the step to the transition on input symbol $y[p-1]?$, which is true by hypothesis. The true-input branch of the $fB$ rule writes $b$ at the current head of auxiliary tape 2 when $f$ is true, and at the head of tape 1 when $f$ is false; it otherwise leaves the auxiliary tapes idle and enters $fA$ with the original flag and bit vector. Applying the action to the configuration (`tact_idle_apply`) translates these writes into updates at the current tape-head positions. The input head moves from $p$ to $p+1$ (`moveInputPos_fpos`). The update at the end of a buffered word is exactly the buffer representing that word with $b$ appended (`bufferTape_write`); separating the two values of $f$ gives the claimed tape contents.

**Key facts.** `Complexity.Meyer.pcfg_step`, `Complexity.Meyer.tact_idle_apply`, `Complexity.Meyer.moveInputPos_fpos`, `Complexity.Meyer.bufferTape_write`.
