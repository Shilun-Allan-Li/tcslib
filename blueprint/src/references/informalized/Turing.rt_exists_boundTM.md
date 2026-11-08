<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_exists_boundTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded binary-writing machine

**Claim.** There is a finite-state machine that writes the binary expansion of $|x|+1$ on tape 0 within linear time, does not reach its exit state earlier, and keeps all work-tape heads within the stated radius.

**Proof.** Take the input-length machine supplied by `exists_inputLengthTM`. It writes the binary expansion of $|x|$ on tape 0, reaches its exit state for the first time within $C(|x|+1)$ steps, and has the stated head-radius bound in terms of the binary length of $|x|$. The proof then appends a successor-increment machine, using `rt_copy_seam` to compose the two runs. At the boundary, the input-length machine’s endpoint agrees with the increment machine’s required initial format: the tape contains the buffer for the bits of $|x|$ on the relevant offsets, with blank cells beyond the word, as verified in the proof’s framing argument. The increment-run theorem (`rt_succ_run`) changes that word to the bits of $|x|+1$, reaches its exit for the first time, and bounds its head movement by the old word length plus four. The bit-length monotonicity and size estimate show that both component radii fit within $B=(C+20)((|x|+1).bits.length+1)$ and that the total time is at most $(C+20)(|x|+1)$. The seam theorem supplies the combined endpoint, first-exit property, and radius bound. At the endpoint, the increment machine’s buffer update is exactly the binary expansion of $|x|+1$; blankness outside the intended tape interval and the endpoint description show that all other tape contents agree with the required configuration.

**Key facts.** `Turing.exists_inputLengthTM`, `Turing.rt_succ_run`, `Turing.rt_succWord_bits`, `Turing.rt_copy_seam`.
