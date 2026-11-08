<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine.lean :: BoolCircuit.CircuitEval.app_walk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a value to the computation tape

**Claim.** Starting from the append state, after $r+1$ steps the machine has appended $v$ to the values tape, erased marks from $h$ through the old tape length, returned to the value-rewind state for gate parsing, and left the input position and output unchanged, with both work-head positions at the old tape length minus one.

**Proof.** Induct on $r$, using $h+r=|\mathrm{vals}|$. When $r=0$, this equality gives $h=|\mathrm{vals}|$. One machine step in the append state writes $v$ at that position, clears the mark there, and enters value rewind. The buffer-tape append identity (`Turing.FinTM.bufferTape_append`) identifies the resulting tape with the representation of $\mathrm{vals}++[v]$; the definition of erasing marks shows that the mark tape agrees with erasing the interval consisting only of the endpoint. The heads and untouched input and output have the stated positions and contents.

For the successor case, $h<|\mathrm{vals}|$, so the current value-tape cell contains a symbol. The append transition clears the mark at $h$ and advances the work heads one place. The induction hypothesis now applies at position $h+1$, with the updated mark tape and with one fewer remaining step, since $(h+1)+r=|\mathrm{vals}|$. The successor-step law for machine runs (`Turing.MultiTapeTM.runFrom_succ_eq_step`) justifies splitting off this first transition. The single-step description (`BoolCircuit.CircuitEval.step_cf`) gives its precise effect; the buffer-tape lookup fact (`Turing.FinTM.bufferTape_nat`) supplies the symbol at the current natural-number position. Finally, erasing after clearing position $h$ agrees with erasing the full interval from $h$ onward, and the work-head arithmetic gives the asserted final position. The zero-run identity (`Turing.MultiTapeTM.runFrom_zero`) supplies the base case’s run interpretation, while a zero head movement leaves the input position unchanged (`Turing.moveInputPos_zero`).

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `BoolCircuit.CircuitEval.step_cf`, `Turing.FinTM.bufferTape_append`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.FinTM.bufferTape_nat`, `Turing.moveInputPos_zero`.
