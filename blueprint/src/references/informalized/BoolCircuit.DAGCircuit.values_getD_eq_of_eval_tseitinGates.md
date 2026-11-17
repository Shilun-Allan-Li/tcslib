<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGCircuit.values_getD_eq_of_eval_tseitinGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tseitin assignments determine circuit values

**Claim.** If an assignment satisfies the conjunction of the Tseitin clauses for every gate of a Boolean directed acyclic circuit with fan-in at most two, then at every circuit vertex the value computed from the input assignment equals the assignment's value at that vertex.

**Proof.** First, satisfaction of the conjunction of all gate clauses is equivalent to satisfaction of the Tseitin clauses for each individual gate (\texttt{eval\_tseitinGates}). We prove the claimed agreement by strong induction on the vertex index. For an input vertex $v<n$, the computed value is the assigned input value, by the input-value property (\texttt{values\_getD\_input}).

For a gate vertex, write $v=n+i$. The range assumption gives $i<|C.\mathrm{gates}|$. The computed value there is the evaluation of gate $i$ on the circuit's computed values (\texttt{values\_getD\_gate}). Every argument $u$ of this gate is less than $n+i$ by acyclicity, so the induction hypothesis says the computed value at $u$ equals $a(u)$. The gate's Tseitin clauses are satisfied, and the local Tseitin equivalence (\texttt{eval\_tseitin}) then identifies $a(n+i)$ with evaluation of that gate on the computed argument values. This yields the required agreement at $v$.

**Key facts.** `BoolCircuit.eval_tseitinGates`, `BoolCircuit.DAGCircuit.values_getD_input`, `BoolCircuit.DAGCircuit.values_getD_gate`, `BoolCircuit.DAGGate.eval_tseitin`.
