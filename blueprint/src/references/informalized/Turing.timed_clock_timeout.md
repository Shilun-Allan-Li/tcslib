<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_clock_timeout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timeout at zero budget

**Claim.** If the four-tape configuration is in the pending-action control and the clock word has value zero, then after exactly $2|bs|+3$ steps the timed interpreter is halted and its output is $[0]$.

**Proof.** By the zero-value characterization of the borrow operation, the borrow of the clock word with initial carry has an outgoing carry (the fact `timedBorrow_underflow`). The timed interpreter first runs for $2|bs|+2$ steps through the clock pass, reaching the borrow phase with this carry; this is the result asserted by `timed_clock_pass`. One further step therefore detects underflow, halts, and emits the bit $0$. To see that the clock has been fully traversed at this point, the borrow operation preserves the word's length (`timedBorrow_length`), so the clock head is at the end of a word of length $|bs|$ and tape 4 reads no symbol. The buffer lookup at this nonnegative position is the corresponding list entry (`bufferTape_nat`), which is absent beyond the end. Thus the interpreter takes the underflow transition, whose action halts and appends false to the initially empty real output. The run-length decomposition is justified by the one-step extension law for runs (`runFrom_succ_eq_step'`).

**Key facts.** `Turing.timedBorrow_underflow`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.timed_clock_pass`, `Turing.timedBorrow_length`, `Turing.FinTM.bufferTape_nat`.
