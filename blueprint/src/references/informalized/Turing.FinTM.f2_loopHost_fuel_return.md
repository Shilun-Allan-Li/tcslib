<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_fuel_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fuel Tape Return

**Claim.** For every $j\le |w|$, the specified phase-3 configuration with counter word $w$, blank payload, and both heads at $j-1$ reaches phase 4 after $j+1$ steps, preserving the counter word, blank payload, and output, with both heads at zero.

**Proof.** Proceed by induction on $j$. At $j=0$, both heads start at $-1$, where the counter tape is blank by the negative-index buffer fact (`bufferTape_left`). The phase-3 transition therefore moves both heads right and enters phase 4; the control-action application rule (`f2_loopControl_apply`) gives heads at zero and leaves the words and output unchanged.

For the successor case, the head position $(j+1)-1$ simplifies to $j$. Since $j<|w|$, the counter tape contains the $j$th bit there by the natural-index buffer identity (`bufferTape_nat`). The phase-3 transition moves both heads left and stays in phase 3, preserving the tapes and output. Applying the induction hypothesis from the resulting configuration completes the run; the bound needed to apply it follows from $j+1\le |w|$. The run-length decomposition (`runFrom_succ_eq_step`) and its zero-time base (`runFrom_zero`) identify these successive steps with the claimed total of $j+2=(j+1)+1$.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.f2_loopFrame_counter`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.f2_loopControl_apply`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
