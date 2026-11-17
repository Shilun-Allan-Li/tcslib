<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean :: Complexity.PathHard.edge_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Edges from the Initial Vertex

**Claim.** There is an edge from vertex $0$ to vertex $v+2$ at radius $s$ exactly when the encoding of $x$, configuration code $v$, and radius $s$ belongs to the machine's initial-configuration language.

**Proof.** Unpack the three edge cases. The accepting case is impossible because it requires $2\le 0$, and the step case is impossible for the same reason. The initial-configuration case remains, with target bound $2\le v+2$ automatic and code $(v+2)-2=v$. Hence it is exactly membership in the stated initial-configuration language. Conversely, that membership, together with the automatic target bound, gives the initial-configuration edge case.
