<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Uniform.lean :: BoolCircuit.DAGCircuit.size_le_length_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bounded by encoding length

**Claim.** The size of a circuit is at most the length of its encoding.

**Proof.** The encoding of a list of gates has length at least the number of gates plus one (`length_encodeList_ge`). The circuit encoding also includes the encoding of the input count, whose length is at least that count. Adding these contributions bounds the circuit size, the input count plus gate count, by the total encoding length.

**Key facts.** `BoolCircuit.length_encodeList_ge`.
