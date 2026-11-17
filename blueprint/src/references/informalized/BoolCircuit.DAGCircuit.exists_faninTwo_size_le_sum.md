<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/BookModelBasics.lean :: BoolCircuit.DAGCircuit.exists_faninTwo_size_le_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binarization with a Size Bound

**Claim.** A well-formed circuit can be replaced by an equivalent well-formed circuit with at most two arguments per gate and size at most $n+\sum_{g\in C}\max(1,\ell(g)-1)$.

**Proof.** Take the circuit obtained by binarizing $C$. The binarization preserves well-formedness and ensures that each gate has at most two arguments (`BoolCircuit.DAGCircuit.binarize_isFaninTwo`). It computes the same function as $C$ on every input (`BoolCircuit.DAGCircuit.binarize_eval`). Its size satisfies the stated sum bound (`BoolCircuit.DAGCircuit.binarize_size_le_sum`). Together these properties give the required circuit.

**Key facts.** `BoolCircuit.DAGCircuit.binarize_isFaninTwo`, `BoolCircuit.DAGCircuit.binarize_eval`, `BoolCircuit.DAGCircuit.binarize_size_le_sum`.
