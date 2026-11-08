<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopHost_reject -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejecting round debits or halts

**Claim.** From the specified non-startup call with empty body output, the host performs the fixed-width decrement of the counter word; on success it reaches the released call with the anchor state and decremented counter, and on underflow it halts with the mode-dependent output, within the stated time bound.

**Proof.** Write the initial host configuration as a phase-seven frame. The frame description (`loopCall_frame`) identifies its flag as false, its counter as the given word, and its payload as empty. One host step clears the flag and enters phase eight (`loopControl_apply`, together with the flag-clearing fact `loopFlag_clear`). The borrow routine (`loopHost_borrow`) then performs the binary decrement: after at most $2\,\mathrm{loopBorrowPos}(w)+2$ steps, it has either entered the non-startup call with the decremented word, or reached phase eleven when the decrement underflows. Since `loopBorrowPos(w)\le |w|` (`loopBorrowPos_le`), the successful branch takes at most $2|w|+3$ total steps, including the initial step. In that branch, re-framing the resulting body state, release bit, flag, and counter gives exactly the specified call (`loopCall_reframe`).

If decrementing underflows, one further control step halts the host and emits false in ordinary mode, while emitting nothing in find mode. The two cases of the mode give the claimed halted configuration and output. The respective time bounds are at most $2|w|+3$ and $2|w|+4$, hence both satisfy the asserted bound.

**Key facts.** `Turing.FinTM.loopCall_frame`, `Turing.FinTM.loopFrame_flag`, `Turing.FinTM.loopControl_apply`, `Turing.FinTM.loopFlag_clear`, `Turing.FinTM.loopHost_borrow`, `Turing.FinTM.loopBorrowPos_le`, `Turing.FinTM.loopCall_reframe`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
