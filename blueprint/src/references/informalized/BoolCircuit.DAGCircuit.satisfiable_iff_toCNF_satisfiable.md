<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGCircuit.satisfiable_iff_toCNF_satisfiable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit and CNF Satisfiability

**Claim.** If every gate has at most two input vertices, the circuit is satisfiable exactly when its associated CNF formula is satisfiable.

**Proof.** For the forward direction, take an input assignment making the circuit output true and assign each CNF variable the value of the corresponding vertex in the circuit's evaluation. The Tseitin gate clauses are all satisfied by these vertex values (`eval_tseitinGates_values`), and the output clause is satisfied because the circuit output is true. Hence the CNF is satisfiable. Conversely, take an assignment satisfying the CNF. Its conjunction of clauses yields both a satisfying assignment for the Tseitin gate clauses and a true output clause. The gate clauses force the assignment's values on all circuit vertices to agree with evaluation from its input values (`values_getD_eq_of_eval_tseitinGates`). In particular, the designated output agrees; since the output clause says that value is true, those input values satisfy the circuit.

**Key facts.** `BoolCircuit.DAGCircuit.eval_tseitinGates_values`, `BoolCircuit.DAGCircuit.values_getD_eq_of_eval_tseitinGates`.
