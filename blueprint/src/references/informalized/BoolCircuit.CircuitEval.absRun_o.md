<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean :: BoolCircuit.CircuitEval.absRun_o -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance in output-index parsing

**Claim.** The output-index-reading run accepts exactly when its input is a unary code of some length $r$ followed by a false bit, and the value at position $j+r$ exists and is true.

**Proof.** Induct on the input string. The empty string cannot accept, and it cannot be a unary code terminated by false. If the first bit is false, acceptance is possible only when the value at the current position $j$ exists and is true; any additional input after that terminator rejects. This is exactly the characterization with $r=0$. Conversely, that witness forces the same transition and acceptance. If the first bit is true, the evaluator advances its position from $j$ to $j+1$ and continues in the same phase. If the current value is absent, the run rejects and no witness can satisfy the required index bound. Otherwise apply the induction hypothesis at $j+1$. A witness of length $r$ there becomes one of length $r+1$ in the original input; conversely, any valid original witness must have positive length, and removing its first true bit gives the witness for the suffix. The index identities $j+(r+1)=(j+1)+r$ complete both directions.
