<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean :: Complexity.PathHard.not_edge_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No edge from vertex one

**Claim.** For every machine, input, and radius, there is no edge from vertex $1$ to any vertex $v$.

**Proof.** Unpack the three possible edge clauses. The first requires the source to equal $0$, the second requires it to be at least $2$, and the third also requires it to be at least $2$. Each contradicts the source value $1$.
