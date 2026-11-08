<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang.lean :: BoolCircuit.DAGCircuit.ofParts_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reconstruction from circuit parts

**Claim.** Constructing a circuit from the number of inputs, the gate list of a given circuit, and its output index returns that circuit.

**Proof.** The given circuit already satisfies the two conditions required for construction: its gates obey the topological ordering constraint, and its output index is valid. Consequently, the construction's defining conditional takes its valid branch and returns the circuit with exactly those gates and that output index.
