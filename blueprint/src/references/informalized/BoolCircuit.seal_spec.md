<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.seal_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Specification of circuit sealing

**Claim.** Sealing every non-output vertex below the circuit size that has fanout zero yields a strict gate extension that is acyclic, has a valid output, and preserves the circuit's output value on every Boolean input.

**Proof.** Apply the general sealing specification `sealGates_spec` to the circuit's gate list, output, and dead-vertex list. The circuit supplies the required acyclicity and valid-output hypotheses. For any index in the dead-vertex list, the characterization of membership says it is below the circuit size (and also differs from the output and has fanout zero); in particular, it is a valid index for sealing (`DAGCircuit.mem_deadVertices`). The general specification then gives the strict extension, acyclicity, valid new output, and equality of output values for every Boolean input.

**Key facts.** `BoolCircuit.DAGCircuit.mem_deadVertices`, `BoolCircuit.sealGates_spec`.
