<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGCircuit.lean :: BoolCircuit.DAGCircuit.values_getD_input -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Computed values at input vertices

**Claim.** At every input vertex $i$, the list of values computed by the circuit has value $x(i)$.

**Proof.** The initial list of values is the list of input-assignment values, and executing gates only appends entries, so positions already present in the initial list retain their values (\texttt{runWith\_getD\_of\_lt}). Since $i$ is an input index, it lies within that initial list; reading its entry gives precisely $x(i)$.

**Key facts.** `BoolCircuit.runWith_getD_of_lt`.
