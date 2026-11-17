<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/HardFunctions.lean :: BoolCircuit.encodeCircuit_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Circuit Encoding

**Claim.** For any natural number $n$, two circuit trees on $n$ variables with the same Boolean-list encoding are equal.

**Proof.** Let $C$ and $D$ be circuit trees whose encodings agree. The read-back theorem for a circuit encoding says that, with enough fuel, reading the encoding of a circuit returns that circuit together with whatever suffix was appended (BoolCircuit.readCircuit_encodeCircuit). Apply it to each encoding with fuel equal to its length and with empty suffix. In both cases the suffix is empty, so reading the common encoded list returns both $C$ and $D$ with empty suffix. Since the read-back results are equal, their circuit components agree, and hence $C=D$.

**Key facts.** `BoolCircuit.readCircuit_encodeCircuit`.
