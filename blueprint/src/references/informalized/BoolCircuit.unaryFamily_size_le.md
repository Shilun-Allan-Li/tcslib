<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: BoolCircuit.unaryFamily_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Bound for the Unary Family

**Claim.** For every language $L$ of Boolean words and every input length $n$, the circuit in the associated unary family has size at most $2$.

**Proof.** Split according to whether the length-$n$ all-true word belongs to $L$. If it does, the unary family’s circuit is the all-ones circuit (`BoolCircuit.unaryFamily_circuit_of_mem`), whose size is $1$ (`BoolCircuit.allOnesCircuit_size`), so it is at most $2$. If it does not, the circuit is the constant-zero circuit (`BoolCircuit.unaryFamily_circuit_of_not_mem`), whose size is $2$ (`BoolCircuit.constZeroCircuit_size`). The desired bound follows in both cases.

**Key facts.** `BoolCircuit.unaryFamily_circuit_of_mem`, `BoolCircuit.allOnesCircuit_size`, `BoolCircuit.unaryFamily_circuit_of_not_mem`, `BoolCircuit.constZeroCircuit_size`.
