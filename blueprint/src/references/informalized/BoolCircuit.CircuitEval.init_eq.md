<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.init_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial machine configuration

**Claim.** For either Boolean mode and every input word, the evaluator's initial configuration is the configuration in state $\mathrm{rd1}(\mathrm{n0})$, with input head at position $1$, blank work tapes, work heads at position $0$, and empty output.

**Proof.** Unfold the machine's initial configuration and the encoding of a scan configuration. Both have the same state, input position, work-head positions, and output. The value tape is blank by the fact that a buffer tape built from the empty word is everywhere blank (`Turing.FinTM.bufferTape_nil`); the mark tape is likewise blank because its initial count is zero. Thus the configurations agree in every component.

**Key facts.** `Turing.FinTM.bufferTape_nil`.
