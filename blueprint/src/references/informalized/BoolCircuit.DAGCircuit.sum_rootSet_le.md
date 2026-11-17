<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/FormulaFanOut.lean :: BoolCircuit.DAGCircuit.sum_rootSet_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on root unfolding sizes

**Claim.** For every $k$ up to the number of gates, the sum of the unfolded sizes of the roots among vertices $[n,n+k)$ is at most $3k$.

**Proof.** Use induction on $k$. At $k=0$ the interval is empty, so the sum is zero. For the step from $k$ to $k+1$, let $g$ be gate $k$. The new root set consists of the new vertex $n+k$, together with the old roots that are not arguments of $g$ (`rootSet_succ`). Thus the new sum is the old-root sum with the contribution of old roots read by $g$ removed, and with the unfolding size of $n+k$ added. The old roots split into those read by $g$ and those not read by it, so the induction bound controls the latter sum by $3k$. The read roots are exactly the arguments of $g$ that are at least $n$: each such argument lies below $n+k$ by the circuit's acyclicity condition, and the fanout bound ensures it was a root among the first $k$ gates. In the reverse direction, if an old root is read by $g$, the total fanout decomposition into the first $k$ gates, gate $g$, and the remaining gates, together with the assumed fanout bound of one, forces its occurrences in the first $k$ gates to be zero. This decomposition follows from additivity of fanout over concatenated gate lists (`fanoutIn_append`) and the single-gate fanout formula (`fanoutIn_singleton`). Finally, the unfolding-size estimate for gate $k$ bounds the new vertex's size by $3$ plus the sum of the unfolded sizes of precisely those arguments. These argument contributions cancel the removed-root sum, leaving at most $3k+3=3(k+1)$.

**Key facts.** `BoolCircuit.DAGCircuit.rootSet_succ`, `BoolCircuit.fanoutIn_append`, `BoolCircuit.fanoutIn_singleton`, `BoolCircuit.DAGCircuit.unfoldSize_gate_le`.
