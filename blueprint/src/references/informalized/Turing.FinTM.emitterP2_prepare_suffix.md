<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_prepare_suffix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copying the Suffix

**Claim.** For every $j\le |w\mathbin{\mathrm{drop}}|s||$, after $j$ steps the machine has copied the first $j$ symbols of that suffix onto the third tape, while preserving the candidate and copy tapes, phase, flag, and specified work-head positions.

**Proof.** We induct on $j$. At $j=0$, no symbols have been copied; the initial frame already has an empty suffix tape, and the input head and work heads are at the stated positions.

For the step from $j$ to $j+1$, the bound implies that the next suffix symbol exists and that $s.length+j<w.length$. The input-head position is `splitPos w (s.length+j)`, so `splitPos_read` identifies the input symbol there as the $(j+1)$st symbol of the suffix. The phase-$1$ transition writes that symbol at position $j$ of the third tape, moves the input head one position right, and advances the third-tape head to $j+1$; it leaves the other tapes and heads alone. The new tape contents are exactly the first $j+1$ symbols: `bufferTape_append` identifies writing the next symbol at the current end with appending it to the stored prefix. Meanwhile `splitPos_succ` gives the new saturated input-head position. The run equation `runFrom_succ_eq_step'` combines this one transition with the induction hypothesis, proving the result.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.splitPos_read`, `Turing.FinTM.bufferTape_append`, `Turing.FinTM.splitPos_succ`.
