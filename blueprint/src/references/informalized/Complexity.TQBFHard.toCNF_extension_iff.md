<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardTseitin.lean :: Complexity.TQBFHard.toCNF_extension_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit extension and CNF satisfiability

**Claim.** There is an assignment extending the first $n$ values of $\sigma$ and satisfying the circuit's CNF encoding exactly when the circuit evaluates to true on those input values.

**Proof.** For the forward direction, take an extending assignment $\tau$ satisfying the CNF. The CNF consists of the clause asserting that the output vertex is true together with the Tseitin clauses for all gates. The gate clauses force each vertex value in the circuit evaluation to agree with its value under $\tau$ (values_getD_eq_of_eval_tseitinGates). Since $\tau$ agrees with $\sigma$ on the input indices, the circuit's evaluated input list is therefore the same for both assignments. The output clause then says that the circuit evaluates to true. For the reverse direction, define $\tau(v)$ to be the value at vertex $v$ in the circuit evaluation on the input assignment from $\sigma$. The input-value property (values_getD_input) shows that $\tau$ agrees with $\sigma$ below $n$. The Tseitin clauses are satisfied by the gate values (eval_tseitinGates_values), and the assumed true circuit output satisfies the output clause. Thus the whole CNF is satisfied.

**Key facts.** `BoolCircuit.DAGCircuit.values_getD_eq_of_eval_tseitinGates`, `BoolCircuit.DAGCircuit.values_getD_input`, `BoolCircuit.DAGCircuit.eval_tseitinGates_values`.
