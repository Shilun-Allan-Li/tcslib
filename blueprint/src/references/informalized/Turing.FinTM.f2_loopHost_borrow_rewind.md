<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_borrow_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind after borrowing

**Claim.** For every $j\le |w|$, after $j+1$ steps from the specified rewind frame, the counter contents are unchanged, its head is at zero, and the machine has reached the return call state if success is true or phase 11 otherwise, with the other stated frame data preserved.

**Proof.** Induct on $j$. At $j=0$, the counter head is at $-1$, where the buffer tape reads blank (`bufferTape_left`); the phase 9 or 10 transition moves it right to zero and enters the required return state or phase 11. For the successor case, the head is at $j$, and the bound on $j$ ensures this position contains the corresponding symbol of $w$ (`bufferTape_nat`). The control transition moves the head one place left without changing the tape contents or other frame data. The induction hypothesis applies to the resulting frame with head at $j-1$, completing the rewind. The frame updates in these cases are given by the control-transition calculation (`f2_loopControl_apply`), while the zero-step and successor-run identities (`runFrom_zero`, `runFrom_succ_eq_step`) relate these transitions to the stated run lengths.

**Key facts.** `Turing.FinTM.bufferTape_left`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.f2_loopControl_apply`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
