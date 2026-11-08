<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_finish_arg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Argument Scan of the Finalizer

**Claim.** For a decomposition $\mathrm{arg}=\mathrm{pre}\,\mathrm{suf}$, starting the finalizer in state $1$ with the specified tape contents and heads, after $|\mathrm{pre}|+1$ steps it reaches state $2$, erases the argument tape in install mode, returns its head to the origin, and moves the capture head one cell left. The capture tape and output are unchanged.

**Proof.** Induct on $\mathrm{pre}$ by removing its last letter. If $\mathrm{pre}$ is empty, the argument head starts at $-1$, where a buffered word has no symbol; the state-$1$ transition therefore changes to state $2$ and moves the heads to the required positions. The zero-step run is the initial configuration, the successor-run identity expresses this single transition, and a zero input movement preserves the input-head position (`runFrom_zero`, `runFrom_succ_eq_step`, `moveInputPos_zero`). For the inductive step, write $\mathrm{pre}=w b$. Since $\mathrm{arg}=w b\,\mathrm{suf}$, the symbol at cell $|w|$ is $b$ (`bufferTape_nat`). In state $1$ the machine reads that symbol, moves the argument head left, and, in install mode, erases the cell it just read. Erasing the last cell of a buffered word leaves precisely the buffer for the shorter prefix (`emCall_erase_last`); in emit mode the tape is left unchanged. Thus one transition takes the configuration for $w b$ to the configuration for $w$, with the capture head unchanged. The lengths satisfy $|w b|-1=|w|$, so the induction hypothesis supplies the remaining $|w|+1$ steps, giving the claimed total.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_nat`, `Turing.FinTM.emCall_erase_last`.
