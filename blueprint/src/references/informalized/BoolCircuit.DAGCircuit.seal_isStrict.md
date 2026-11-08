<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.DAGCircuit.seal_isStrict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Strictness after sealing

**Claim.** If every gate of a finite Boolean circuit has distinct arguments and the required arity, then sealing preserves these gate properties and ensures every nonoutput vertex is read by some gate.

**Proof.** The sealing specification says that the sealed gate list is the original list followed by an extension whose gates are all strict (`seal_spec`). Thus any gate in the sealed list is either an original gate, strict by hypothesis, or one of the added gates, strict by the specification. For the read condition, `sealGates_read` guarantees positive fanout in the sealed circuit for every in-range vertex other than its output, provided the vertex was not in the list of vertices being sealed. The sealed list here is the circuit’s dead vertices. By the characterization of that list (`DAGCircuit.mem_deadVertices`), membership means the vertex is in range, is not the original output, and has zero original fanout. Consequently, a vertex in range and different from the original output but not in the dead-vertex list has positive original fanout; the sealing read result applies. A vertex equal to the original output also cannot be a newly sealed output with a different value, by the sealing construction’s read guarantee. Hence every in-range vertex other than the sealed output has positive fanout in the sealed circuit.

**Key facts.** `BoolCircuit.seal_spec`, `BoolCircuit.sealGates_read`, `BoolCircuit.DAGCircuit.mem_deadVertices`.

**Caveat.** The supplied proof applies `sealGates_read` with a side condition excluding the original dead-vertex list, while the theorem concerns vertices distinct from the sealed output. The payload omits the full statement of `sealGates_read`’s proof and the detailed sealing construction needed to justify that side condition for all such vertices; the informal justification above follows the intended dead-vertex argument.
