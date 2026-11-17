<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: BoolCircuit.unaryFamily_onlyUsesGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate Set of the Unary Family

**Claim.** For any language $L$ of Boolean words, every circuit assigned by the unary family uses only identity, NOT, and unbounded fan-in AND gates.

**Proof.** Fix an input length $n$ and split according to whether the length-$n$ all-true word belongs to $L$. In the affirmative case, the unary family’s circuit is the all-ones circuit (`BoolCircuit.unaryFamily_circuit_of_mem`), and the all-ones family uses only the specified standard gates (`BoolCircuit.allOnesFamily_onlyUsesGates`). In the negative case, it is the constant-zero circuit (`BoolCircuit.unaryFamily_circuit_of_not_mem`), which also uses only those gates (`BoolCircuit.constZeroCircuit_onlyUsesGates`). Hence the length-$n$ circuit uses only gates from the specified set in either case; since $n$ was arbitrary, the whole family has the claimed property.

**Key facts.** `BoolCircuit.unaryFamily_circuit_of_mem`, `BoolCircuit.allOnesFamily_onlyUsesGates`, `BoolCircuit.unaryFamily_circuit_of_not_mem`, `BoolCircuit.constZeroCircuit_onlyUsesGates`.
