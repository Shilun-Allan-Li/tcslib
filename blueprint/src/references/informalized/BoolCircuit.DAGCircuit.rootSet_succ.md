<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.DAGCircuit.rootSet_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successive Root Sets

**Claim.** For $k$ below the number of gates, the root set for the first $k+1$ gates is obtained by adjoining vertex $n+k$ to the previous root set after removing vertices read by gate $k$.

**Proof.** The first $k+1$ gates consist of the first $k$ gates followed by gate $k$. Among vertices already in the interval $[n,n+k)$, a vertex is unread by the enlarged list exactly when it was unread by the first $k$ gates and is not an argument of gate $k$. The only additional vertex in the new interval $[n,n+k+1)$ is $n+k$. It is unread by the first $k$ gates because acyclicity puts every argument of those gates below $n+k$; it is also not an argument of gate $k$, since that gate can read only vertices below $n+k$. Thus this new vertex is added to the filtered previous root set, giving the stated equality.

**Key facts.** `BoolCircuit.DAGCircuit.gatesAcyclic_take`, `BoolCircuit.fanoutIn_eq_zero_of_le`, `BoolCircuit.fanoutIn_append`, `BoolCircuit.fanoutIn_singleton`.
