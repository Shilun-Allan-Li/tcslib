<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.place_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Placed Vertices

**Claim.** If $a<n+r+g$, where $g$ is the number of combinational gates, then placing $a$ at stage $k$ gives an index less than $n+(k+1)(r+g)$.

**Proof.** Write $s=r+g$, so $s$ is the sequential circuit's size. If $a<n$, placing it leaves its index unchanged, and $a<n\le n+(k+1)s$. Otherwise, the placement is $a+ks$. The hypothesis gives $a<n+s$, hence $a+ks<n+s+ks=n+(k+1)s$.
