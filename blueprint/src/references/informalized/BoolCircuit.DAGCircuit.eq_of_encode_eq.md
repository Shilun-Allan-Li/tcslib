<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Uniform.lean :: BoolCircuit.DAGCircuit.eq_of_encode_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness from Circuit Encoding

**Claim.** If two directed acyclic Boolean circuits have equal encodings, then they have the same number of inputs, the same ordered gate list, and the same output vertex.

**Proof.** The encoding is a concatenation of three prefix-free components: the input count encoded as a unary string, the gate list encoded using the prefix-free gate encoding, and the output encoded as a unary string. Prefix-freeness of the natural-number encoding identifies the first component and forces the input counts to agree (`BoolCircuit.encodeNat_prefixFree`). Prefix-freeness of list encoding when its element encoding is prefix-free then identifies the gate lists (`BoolCircuit.encodeList_prefixFree`), using prefix-freeness of the gate encoding (`BoolCircuit.DAGGate.encode_prefixFree`). The remaining suffixes are equal; applying prefix-freeness of the natural-number encoding again forces the output vertices to agree.

**Key facts.** `BoolCircuit.encodeNat_prefixFree`, `BoolCircuit.DAGGate.encode_prefixFree`, `BoolCircuit.encodeList_prefixFree`.
