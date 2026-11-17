<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalCorrect.lean :: BoolCircuit.CircuitEval.absRun_u -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance while reading an argument

**Claim.** The argument-reading run accepts exactly when the input consists of a unary code for an index $j+r$, terminated by false, followed by a remainder, where that index is in range and unmarked, and the updated argument-accumulation run accepts on the remainder.

**Proof.** Induct on the input string. An empty input cannot accept. If the first bit is false, the evaluator attempts to read the value at the current position $j$. Acceptance requires that this value exists and that $j$ is not marked. The position is then marked, the accumulator is updated with that value, and the evaluator enters the argument-accumulation phase at position zero on the remaining string. This gives the characterization with $r=0$; conversely, a witness with $r=0$ forces exactly these conditions and this transition. If the first bit is true, a missing value at $j$ makes the run reject, so assume the value exists. The evaluator advances to $j+1$ while staying in the argument-reading phase. Apply the induction hypothesis to the suffix: its unary-code length $r$ becomes $r+1$ in the original string. The index identities $(j+1)+r=j+(r+1)$ preserve the bounds, unmarked condition, and accumulator update in both directions. Thus the witness code and remainder describe exactly the evaluator’s behavior.
