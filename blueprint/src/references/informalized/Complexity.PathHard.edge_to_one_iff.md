<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean :: Complexity.PathHard.edge_to_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Edges into the Accepting Vertex

**Claim.** There is an edge from vertex $u+2$ to vertex $1$ at radius $s$ exactly when the encoding of $x$, configuration code $u$, and radius $s$ belongs to the machine's accepting-configuration language.

**Proof.** Unpack the three edge cases. The initial-vertex case is impossible because it requires $u+2=0$, and the step case is impossible because it requires $1\ge 2$. The only possible case is the accepting-configuration case: its source bound holds since $u+2\ge 2$, its target is exactly $1$, and its code is the stated encoding because $(u+2)-2=u$. Conversely, membership in the accepting language supplies this case of the edge definition; the source bound again follows from $u+2\ge 2$.
