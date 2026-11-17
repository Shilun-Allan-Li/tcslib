<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_fuel_copy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fuel Tape Copying

**Claim.** For each prefix $p$, the phase-2 host configuration described in the statement reaches phase 3 after $|\mathrm{rest}|+1$ steps, with the counter tape storing $p$ concatenated with the remainder, the payload blank, the prescribed head positions, and the other specified components unchanged.

**Proof.** Induct on the remainder. If it is empty, one step sees a blank on the payload tape, moves the heads left, and switches to phase 3. The payload-read identity (`f2_loopFrame_payload`) identifies the scanned symbol, while the copy-read and copy-final facts (`f2_loopCopy_read`, `f2_loopCopy_final`) show that the source is exhausted and blank. The control-action application rule (`f2_loopControl_apply`) gives the resulting frame and heads.

For a remainder beginning with bit $b$, the copy-read identity (`f2_loopCopy_read`) makes the transition read $b$. The phase-2 action writes $b$ onto the counter tape, erases the current payload cell, advances both heads, and stays in phase 2. The frame-action rule (`f2_loopControl_apply`), the copy-erasure identity (`f2_loopCopy_erase`), and the append/update identity (`bufferTape_append`) show that this single step changes the state to the induction hypothesis's configuration with prefix extended by $b$. The induction hypothesis copies the remaining suffix in the stated number of steps. The recursive run decomposition (`runFrom_succ_eq_step`) and the zero-step identity (`runFrom_zero`) account for the one initial step and complete the total of $|\mathrm{rest}|+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.FinTM.f2_loopFrame_payload`, `Turing.FinTM.f2_loopCopy_read`, `Turing.FinTM.f2_loopControl_apply`, `Turing.FinTM.f2_loopCopy_final`, `Turing.FinTM.f2_loopCopy_erase`, `Turing.FinTM.bufferTape_append`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
