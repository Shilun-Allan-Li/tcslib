<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.DAGCircuit.seal_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for the sealed circuit

**Claim.** The size of a circuit after sealing is at most four times the size of the original circuit.

**Proof.** Sealing adds exactly three gates for each vertex in the list being sealed: the resulting gate count is the original gate count plus three times the list length (`sealGates_length`). The dead-vertex list is obtained by filtering the vertices in the range from zero to the original size, so its length is at most the original size. Substituting this bound into the gate-count formula, and recalling that size is the number of inputs plus the number of gates, gives the claimed bound by elementary arithmetic.

**Key facts.** `BoolCircuit.sealGates_length`.
