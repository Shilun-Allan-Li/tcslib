<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.bufferedScanCfg_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind scan reaches the second phase

**Claim.** For every $j\le |y|$, running the buffered composition for $j+1$ steps from the rewind-scan configuration at buffer-head position $j-1$ reaches the second-phase initialization of $M_2$ on $y$, with true arrival tag, physical input position $p$, and the chosen left-block data unchanged.

**Proof.** Induct on $j$. When $j=0$, the buffer head is at $-1$, where the buffer reads blank (`bufferTape_left`). Thus the rewind-scan state immediately detects the left boundary and begins the second phase. Its transition leaves the physical input position unchanged because a zero move fixes every valid position (`moveInputPos_zero`); the tape blocks and head positions then agree with the second-phase initialization, whose virtual input head starts at position $1$ and whose arrival tag is true. For the successor case, the bound $j+1\le |y|$ guarantees that cell $j$ contains the bit $y[j]$. At the scan configuration with head at $j$, the buffer read is therefore nonblank (`bufferTape_nat`), so the scan moves one cell left and remains in rewind mode. This step preserves the left block, leaves the physical input head fixed, and places the buffer head at $j-1$. The run of length $j+2$ is consequently this one step followed by the $j+1$-step run covered by the induction hypothesis (`runFrom_succ_eq_step`).

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
