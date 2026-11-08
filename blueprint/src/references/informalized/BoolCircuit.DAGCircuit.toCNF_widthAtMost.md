<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGCircuit.toCNF_widthAtMost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width bound for the CNF encoding

**Claim.** Every clause in the CNF formula obtained from the circuit contains at most three literals.

**Proof.** The output clause is a single unit clause. Every other clause belongs to the Tseitin encoding of some gate (`exists_of_mem_tseitinGates`), and each clause in a gate's encoding has length at most three (`length_le_of_mem_tseitin`).

**Key facts.** `BoolCircuit.exists_of_mem_tseitinGates`, `BoolCircuit.DAGGate.length_le_of_mem_tseitin`.
