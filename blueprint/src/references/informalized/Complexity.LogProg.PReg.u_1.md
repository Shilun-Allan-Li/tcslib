<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.u_1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Vertex Count

**Claim.** Updating coordinate $1$ of the register vector of a nine-register record $\sigma$ to $z$ gives the register vector of the record obtained by replacing its vertex-count register with $z$.

**Proof.** To prove equality of the two register vectors, compare them at each index $r\in\{0,\ldots,8\}$. At index $1$, both have value $z$. At every other index, the update leaves the original entry unchanged, and replacing the vertex-count field leaves that corresponding entry unchanged as well. Thus the vectors agree at every coordinate.
