<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean :: Complexity.PathHard.not_edge_to_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No edge to vertex zero

**Claim.** For every machine, input, and radius, there is no edge from any vertex $u$ to vertex $0$.

**Proof.** Unpack the three possible edge clauses. The first requires the target to be at least $2$, the second requires it to equal $1$, and the third requires it to be at least $2$. Each contradicts the target value $0$.
