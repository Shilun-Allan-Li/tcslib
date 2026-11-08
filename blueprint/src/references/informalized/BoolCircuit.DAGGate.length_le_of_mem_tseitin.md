<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGGate.length_le_of_mem_tseitin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tseitin Clause Length Bound

**Claim.** Every clause in the Tseitin encoding of any gate has length at most three.

**Proof.** Write the gate as a kind and an argument list, and split by argument-list length. With zero inputs, the encoding clauses are singletons; with one input, they have length two; with two inputs, they have length three. If there are at least three inputs, the encoding is empty, so there are no clauses to check. These cases establish the bound.
