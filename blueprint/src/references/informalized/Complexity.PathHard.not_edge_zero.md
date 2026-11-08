<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean :: Complexity.PathHard.not_edge_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No edge from zero to small vertices

**Claim.** For every machine, input, and radius, if $v<2$, there is no edge from vertex $0$ to vertex $v$.

**Proof.** Unpack the possible edge clauses. The second and third clauses require the source to be at least $2$, contradicting that it is $0$. The first requires the target to be at least $2$, contradicting $v<2$.
