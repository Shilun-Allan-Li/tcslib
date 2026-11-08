<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGCircuit.toCNF_length_le_gates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CNF length bound by gate count

**Claim.** The CNF formula obtained from the circuit has length at most four times its number of gates, plus one.

**Proof.** The CNF consists of one unit clause asserting the circuit output, followed by the clauses contributed by the gates. The gate encoding contributes at most four clauses per gate (`length_tseitinGates_le`), so the total length is at most $1+4|C.gates|$.

**Key facts.** `BoolCircuit.length_tseitinGates_le`.
