<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Uniform.lean :: BoolCircuit.DAGCircuit.encode_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Circuit Encoding

**Claim.** For fixed $n$, the Boolean-string encoding is injective on directed acyclic Boolean circuits with $n$ input vertices: equal encodings imply equal circuits.

**Proof.** Suppose two such circuits have equal encodings. The uniqueness theorem for circuit encodings extracts equality of their input counts, gate lists, and output vertices (`BoolCircuit.DAGCircuit.eq_of_encode_eq`). The input counts already agree because both circuits have the fixed count $n$. A circuit is determined by its gate list and output vertex once its input count is fixed, so the two circuits are equal.

**Key facts.** `BoolCircuit.DAGCircuit.eq_of_encode_eq`.
