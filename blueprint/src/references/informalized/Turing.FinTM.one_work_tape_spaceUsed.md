<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.one_work_tape_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Tape Simulation with Space Bound

**Claim.** A finite machine computing a function within time $T$ and using at most $S(|x|)$ space at every time can be replaced by a one-work-tape machine over an enlarged finite alphabet, with the stated quadratic time and linear space bounds.

**Proof.** Split according to the number of work tapes and whether the alphabet is inhabited.

1. If there are zero work tapes, use the same alphabet and encoding with the construction that adds an unused tape. The original computation is preserved (`Turing.FinTM.unusedTape_computes`), and the added machine uses exactly one cell of space at every time (`Turing.FinTM.dg_unused_space`). Monotonicity extends its time bound to the claimed quadratic bound (`Turing.FinTM.ComputesInTime.mono`); the constant bounds one cell by $S(|x|)+1$.

2. If there is at least one work tape and the alphabet is inhabited, choose a symbol of the alphabet and construct the sweep simulation. The lemma for all inputs gives the encoded output within $(9k+6)(T(|x|)+1)^2$ steps and bounds space at every time by $(9k+6)(S(|x|)+1)$ (`Turing.FinTM.dg_all_inputs`). The chosen default symbol is used in the simulation's encoding and retraction; the encoding-retraction identity ensures encoded symbols recover their original values (`Turing.FinTM.dgRetract_embed`).

3. If the machine has at least one work tape but the alphabet is empty, every input word is empty, and any output word over that alphabet must also be empty. Use a zero-work-tape machine that halts immediately with empty output; its computation follows from the characterization of computation by halting and output (`Turing.FinTM.computesInTime_iff`). Add an unused tape as in the first case. Its one-cell space bound is at most $S(|x|)+1$, and its time bound is covered by the claimed quadratic bound.

**Key facts.** `Turing.FinTM.unusedTape_computes`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.dg_unused_space`, `Turing.FinTM.dg_all_inputs`, `Turing.FinTM.dgRetract_embed`, `Turing.FinTM.computesInTime_iff`.
