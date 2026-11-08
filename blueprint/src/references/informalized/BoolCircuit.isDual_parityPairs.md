<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.isDual_parityPairs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of Literal Pairs

**Claim.** For each variable, the circuit for its negated literal evaluates to the complement of the circuit for its positive literal.

**Proof.** A pair in the list of parity pairs comes from some variable index $i$ and consists of the positive literal at $i$ followed by the negative literal at $i$. The positive literal evaluates to the assigned value $x(i)$, while the negative literal evaluates to its Boolean complement. Hence the second circuit's value is the complement of the first, as required.
