<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PUniformP.lean :: BoolCircuit.DAGCircuitFamily.IsPUniform.polyTimeReducible_CVAL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reduction to circuit value

**Claim.** For a polynomial-time-uniform family whose circuits are well formed and have at most two inputs per gate, the language accepted by the family is polynomial-time many-one reducible to the Boolean circuit value language for circuits with at most two inputs per gate.

**Proof.** Choose a polynomial-time-uniformity function $f$. Map an input $x$ to the pair encoding of the circuit description $f(1^{|x|})$ and the input $x$. This map is polynomial-time computable: forming the unary string of length $|x|$ is polynomial-time computable (Complexity.polyTimeComputable_unary); applying $f$ to it remains polynomial-time computable by closure under composition; and pairing the resulting description with $x$ is polynomial-time computable (Complexity.PolyTimeComputable.pairEncode, using Complexity.polyTimeComputable_id for the identity map). By uniformity, $f(1^{|x|})$ is exactly the encoding of the circuit for inputs of length $|x|$. The circuit-family membership characterization says that $x$ is accepted precisely when the pair of that circuit's encoding and $x$ belongs to the circuit value language, under the fan-in-two hypothesis (BoolCircuit.DAGCircuitFamily.mem_language_iff_pairEncode_mem_CVAL). Thus the map is a polynomial-time many-one reduction.

**Key facts.** `Complexity.polyTimeComputable_unary`, `Complexity.polyTimeComputable_id`, `Complexity.PolyTimeComputable.comp`, `Complexity.PolyTimeComputable.pairEncode`, `BoolCircuit.DAGCircuitFamily.mem_language_iff_pairEncode_mem_CVAL`.
