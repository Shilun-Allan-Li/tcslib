<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGCircuit.length_depths -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the depth list

**Claim.** For a directed acyclic circuit with $n$ input vertices and gates in topological order, the list of vertex depths has length $n$ plus the number of gates.

**Proof.** The depth list contains one entry for each input vertex and one for each gate. Unfolding its definition therefore gives a list of length $n+C.\mathrm{gates.length}$, as claimed.
