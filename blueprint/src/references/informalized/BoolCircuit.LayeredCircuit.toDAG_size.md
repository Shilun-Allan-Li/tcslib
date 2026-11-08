<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.toDAG_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size of the Converted Circuit

**Claim.** The size of the DAG obtained from the finite layered circuit is the number of inputs plus the size of the layered circuit.

**Proof.** By definition, the DAG size is the number of inputs plus the length of its gate list. The length formula for gates constructed up to depth (\texttt{BoolCircuit.LayeredCircuit.length_gatesUpTo}) identifies that list length with the sum, over layers, of the number of nodes in the next layer. The layered circuit’s size is the cardinality of the dependent sum of exactly those next-layer node types. Since each layer is finite, cardinality of this dependent sum is the sum of their cardinalities. Thus the gate-list length equals the layered circuit size, giving the claimed formula.

**Key facts.** `BoolCircuit.LayeredCircuit.length_gatesUpTo`.
