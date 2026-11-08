<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.mem_dagCktSat_iff_toCNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# DAG Circuit CNF Encoding

**Claim.** For a fan-in-two Boolean DAG circuit, the pair consisting of its variable count and circuit belongs to the set of fan-in-two satisfiable DAG circuits exactly when the circuit's associated CNF has width at most three and is satisfiable.

**Proof.** Rewrite membership in the set as the conjunction of being fan-in-two and being satisfiable (`mem_dagCktSat_iff`). The fan-in-two hypothesis already supplies the first condition. For a fan-in-two circuit, satisfiability is equivalent to satisfiability of its associated CNF (`DAGCircuit.satisfiable_iff_toCNF_satisfiable_of_isFaninTwo`), and that CNF always has width at most three (`DAGCircuit.toCNF_widthAtMost`). Hence the conjunction on the left is equivalent to the width and satisfiability conditions on the right.

**Key facts.** `BoolCircuit.mem_dagCktSat_iff`, `BoolCircuit.DAGCircuit.satisfiable_iff_toCNF_satisfiable_of_isFaninTwo`, `BoolCircuit.DAGCircuit.toCNF_widthAtMost`.
