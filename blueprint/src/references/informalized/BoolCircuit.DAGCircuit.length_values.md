<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGCircuit.length_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the value list

**Claim.** For a directed acyclic circuit with $n$ input vertices and gates in topological order, evaluating the gates in order from any Boolean input assignment produces a list of values of length $n$ plus the number of gates.

**Proof.** The initial list contains the $n$ assigned input values. The circuit evaluation processes each gate by appending exactly one Boolean value to the list accumulated so far. Thus the final list has length $n+C.\mathrm{gates.length}$.
