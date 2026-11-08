<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/DAGFanin.lean :: BoolCircuit.treeCost_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for Tree Cost

**Claim.** For every natural number $k$, the tree cost of $k$ is at most $k+2$.

**Proof.** If $k=0$, the tree cost is $1$, which is at most $2$. If $k\ne0$, its value is $k-1$, which is at most $k+2$.
