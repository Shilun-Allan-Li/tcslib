<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredCircuit.lean :: BoolCircuit.nodeToTreeCircuit_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size bound for tree unrolling

**Claim.** For every node at layer $m$ of a Boolean layered circuit whose gates have arity at most $k$, recursively unrolling the node gives a tree of size at most $(k+1)^m$.

**Proof.** Proceed by induction on the layer, generalizing over the layer bound and node. At layer $0$, unrolling produces a single literal, of size $1=(k+1)^0$. For the step, the unrolling at layer $m+1$ consists of a root node and one recursively unrolled child for each input of the gate at layer $m$. By the induction hypothesis, each child tree has size at most $(k+1)^m$. Thus the sum of the child sizes is at most the number of inputs times $(k+1)^m$. The gate has at most $k$ inputs, so the total size, including the root, is at most $1+k(k+1)^m$. Since $(k+1)^{m+1}= (k+1)(k+1)^m$ and $(k+1)^m\ge 1$, this is at most $(k+1)^{m+1}$.
