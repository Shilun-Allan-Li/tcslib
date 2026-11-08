<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgGate.parse_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing an Encoded Algebraic Gate

**Claim.** For every algebraic gate $g$ and Boolean string $r$, parsing the encoding of $g$ followed by $r$ returns the gate $g$ and leaves $r$ as the remaining string.

**Proof.** Proceed by cases on the gate constructor. For a variable gate, the variable tag directs the parser to decode its unary index; `decodeNat_encodeNat` recovers that index and leaves the suffix $r$. The index is below $n$ because the gate is a variable on $n$ inputs, so the parser returns that variable and the unchanged suffix. For the constant gate, its tag is recognized directly and the parser returns the constant with $r$ remaining. For each of addition, subtraction, and multiplication, the corresponding tag selects the matching binary constructor. Applying `decodeNat_encodeNat` successively to the two encoded node indices recovers both indices and leaves $r$, so the parser returns the original gate and suffix.

**Key facts.** `BoolCircuit.decodeNat_encodeNat`.
