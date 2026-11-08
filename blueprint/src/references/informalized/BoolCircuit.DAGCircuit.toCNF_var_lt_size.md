<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuitSat.lean :: BoolCircuit.DAGCircuit.toCNF_var_lt_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CNF variable indices are bounded

**Claim.** Every literal in every clause of the CNF encoding has variable index strictly less than $\mathrm{size}(C)$.

**Proof.** Separate the output unit clause from the gate clauses. Its only variable is the output vertex, which is below $n+|C.gates|=\mathrm{size}(C)$ by the circuit's output condition. Any other clause comes from the Tseitin encoding of some gate $i$, at index $i<|C.gates|$ (`exists_of_mem_tseitinGates`). Every variable in that gate's clauses is either the fresh variable $n+i$ or one of the gate's arguments (`var_mem_of_mem_tseitin`). The fresh variable is below $n+|C.gates|$. Each argument is below $n+i$ by the circuit's acyclicity condition, hence also below the circuit size.

**Key facts.** `BoolCircuit.exists_of_mem_tseitinGates`, `BoolCircuit.DAGGate.var_mem_of_mem_tseitin`.
