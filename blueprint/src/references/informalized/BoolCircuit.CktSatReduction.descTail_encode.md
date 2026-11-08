<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.descTail_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Description Tail of a Circuit Encoding

**Claim.** For a finite acyclic Boolean circuit with $n$ input vertices, topologically ordered gates reading only earlier vertices, and a circuit-vertex output, the description-tail transducer applied to its encoding returns the unary encoding of the output index.

**Proof.** The transducer ignores the initial unary encoding of the number of inputs: while in state $n$, reading each leading $1$ leaves it in that state and emits nothing (`S_ones`). The following delimiter moves it to state $g$. The gate-list encoding is consumed without output, and the transducer reaches state $o$ at the start of the output-index encoding (`S_gates`). In state $o$, each bit is copied, so the remaining unary encoding is returned unchanged (`S_cons`). This is exactly the unary encoding of the circuit's output index.

**Key facts.** `BoolCircuit.CktSatReduction.S_ones`, `BoolCircuit.CktSatReduction.S_gates`, `BoolCircuit.CktSatReduction.S_cons`.
