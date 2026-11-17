<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.DAGCircuit.succ_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Successor bound

**Claim.** If $d<m$ for a natural number $d$ and gate count $m$, then the successor of $d$ is at most $m$.

**Proof.** The successor of a natural number has value $d+1$. Since $d<m$, discreteness of the natural numbers gives $d+1\le m$, which is the desired bound.
