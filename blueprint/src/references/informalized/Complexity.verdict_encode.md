<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PPolyAdvice.lean :: Complexity.verdict_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit evaluation from its encoding

**Claim.** For a well-formed fan-in-two Boolean circuit $C$ with $m$ inputs and a bit string $x$ of length $m$, evaluating the encoded circuit-input pair returns the value of $C$ on the assignment whose $i$th input is the bit at position $i$ of $x$, using false when absent.

**Proof.** First suppose the circuit evaluates to false. If the encoded pair evaluated to true, the characterization of evaluation on a paired encoding (`BoolCircuit.CircuitEval.verdict_pairEncode`) would supply a circuit and input length with matching encoding whose circuit evaluates to true. Equality of encodings forces the input length and encoded circuit data to agree with those of $C$ (`BoolCircuit.DAGCircuit.eq_of_encode_eq`); injectivity of the encoding identifies the circuits (`BoolCircuit.DAGCircuit.encode_injective`). The characterization would then say that $C$ evaluates to true, contradicting the assumed false value. Thus the encoded pair also evaluates to false. If instead $C$ evaluates to true, the forward direction of the same characterization applies directly with $C$, its fan-in-two hypothesis, its encoding, and the fact that $|x|=m$. It follows that the encoded pair evaluates to true. The two Boolean values therefore agree.

**Key facts.** `BoolCircuit.CircuitEval.verdict_pairEncode`, `BoolCircuit.DAGCircuit.eq_of_encode_eq`, `BoolCircuit.DAGCircuit.encode_injective`.
