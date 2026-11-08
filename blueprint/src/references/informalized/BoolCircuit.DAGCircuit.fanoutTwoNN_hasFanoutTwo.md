<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictFanOut.lean :: BoolCircuit.DAGCircuit.fanoutTwoNN_hasFanoutTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fanout bound after reduction

**Claim.** Every vertex in the fanout-reduced circuit has fanout at most two.

**Proof.** The construction invariant bounds the fanout of every vertex in the constructed gate list by two. The converted circuit uses exactly that gate list, so the bound applies to every vertex of the converted circuit.

**Key facts.** `BoolCircuit.nnGates_inv`.
