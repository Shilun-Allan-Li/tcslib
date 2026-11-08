<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.step_rd1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the First Input Tape

**Claim.** If the bit at index $i$ of $z$ is $b$, then from the stated configuration in phase $q$, one machine step advances the input head from position $i+1$ to $i+2$ and records $q$ and $b$ in the state, leaving tapes, work-head positions, and output unchanged.

**Proof.** At input-head position $i+1$, the scanned symbol is the list entry $z[i]?$, which is $b$ by hypothesis (`Turing.FinTM.inputSymbol_at`). In state $\mathrm{rd1}(q)$, the transition on a bit $b$ moves the input head right and enters $\mathrm{rd2}(q,b)$; it makes no writes, moves neither work head, and emits no output. The one-step configuration update (`BoolCircuit.CircuitEval.step_cf`) translates this action into the resulting configuration. Since the current head position is not the right boundary, moving right advances its position by one (`Turing.moveInputPos_pos_of_ne_right`), giving position $i+2$ as required.

**Key facts.** `BoolCircuit.CircuitEval.step_cf`, `Turing.FinTM.inputSymbol_at`, `Turing.moveInputPos_pos_of_ne_right`.
