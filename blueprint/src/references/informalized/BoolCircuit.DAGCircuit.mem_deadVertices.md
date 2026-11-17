<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StrictSize.lean :: BoolCircuit.DAGCircuit.mem_deadVertices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of dead vertices

**Claim.** A vertex belongs to the list of dead vertices exactly when it is less than the circuit size, differs from the output vertex, and is read by no gate.

**Proof.** The dead-vertex list is obtained by filtering the list of all indices below the circuit size, retaining exactly those that differ from the output and have fanout zero. Membership in that filtered list is therefore equivalent to the three stated conditions.
