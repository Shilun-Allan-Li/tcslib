<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformCanon.lean :: BoolCircuit.DAGCircuitFamily.hasLogspaceAdjacency_canon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical circuits preserve logspace adjacency

**Claim.** If a circuit family has polynomial size and its size, gate-type, and edge languages are in LOGSPACE, then its canonicalized family has the same properties.

**Proof.** Unpack the assumptions: the original family has polynomial-size constants and its three adjacency languages are in LOGSPACE. For each input length, the canonical circuit has the same size as the original, so the same polynomial bound applies. The size language of the canonical family equals the original size language; likewise, for every gate type, the two type languages agree, and the two edge languages agree. Each language-membership conclusion therefore transfers directly from the original family to its canonicalized family. Together these facts give polynomial size and all the required LOGSPACE language conditions.
