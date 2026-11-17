<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGCircuit.values_getD_gate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computed value at a gate vertex

**Claim.** For every gate index $i$ in the circuit and every input assignment, the computed value at vertex $n+i$ equals gate $i$ evaluated on the list of values computed by the circuit.

**Proof.** Executing the gates in order appends the value of gate $i$ after the $i$ earlier gates. Thus the value at position $n+i$ in the full computed list is the value of gate $i$ evaluated on the list produced by executing just the first $i$ gates (\texttt{runWith\_getD\_gate}); the initial list has length $n$. Every argument of gate $i$ is less than $n+i$ by acyclicity. Therefore the prefix list and the full computed list agree at every argument position (\texttt{runWith\_getD\_take}). Evaluation depends only on values at argument positions (\texttt{DAGGate.eval\_congr}), so evaluating gate $i$ on either list gives the same result. Combining these facts proves the claim.

**Key facts.** `BoolCircuit.runWith_getD_gate`, `BoolCircuit.runWith_getD_take`, `BoolCircuit.DAGGate.eval_congr`.
