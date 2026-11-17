<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean :: BoolCircuit.GateKind.decode_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding an encoded gate kind

**Claim.** For every gate kind $k$ and every Boolean list $r$, decoding the encoding of $k$ followed by $r$ returns $k$ together with the remaining list $r$.

**Proof.** There are three gate kinds. Their encodings begin respectively with the two-bit strings $00$, $01$, and $10$. The decoder matches each of these prefixes and returns the corresponding kind together with the untouched suffix. Applying this definition to each encoding gives the stated result.
