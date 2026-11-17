<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRead_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding a doubled bit

**Claim.** When the reader scans a doubled bit $b,b$, after two steps it returns to its scanning control, leaves the stream unchanged, advances the stream cursor by two and the target cursor by one, and changes the target from $v++o$ to $v++b::o.tail$.

**Proof.** At the stream cursor $|u|$, the buffer contains the first copy of $b$; after one rightward move it contains the second copy. The reader’s first transition stores the observed bit in its control state and advances the stream head, without changing either tape. Since the second observed bit agrees with the stored bit, the next transition writes $b$ at the target head, moves both relevant heads right, and returns to the scanning control. The stream buffer itself is unchanged. The target update writes at position $|v|$, so the list of symbols represented by the target becomes $v++b::o.tail$. The two moves of the stream head and the one move of the target head give the asserted cursor positions. The buffer lookup at natural positions is the list-index fact `FinTM.bufferTape_nat`; the run is unfolded into its two transitions using `runFrom_succ_eq_step'` and `runFrom_zero`, and a zero input-head move leaves that head fixed by `moveInputPos_zero`.

**Key facts.** `Turing.FinTM.bufferTape_nat`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.moveInputPos_zero`, `Complexity.clCountTape_eq`, `Complexity.clCountTape_write`.
