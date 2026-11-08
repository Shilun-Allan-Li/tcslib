<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardWalk.lean :: Complexity.PathHard.edge_codes_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Edge and Step Codes

**Claim.** There is an edge from vertex $u+2$ to vertex $v+2$ at radius $s$ exactly when configuration code $u$ can take one machine step to configuration code $v$, with both configurations using radius $s$.

**Proof.** Unpack the three cases in the definition of an edge. The first case would require $u+2=0$, and the second would require $v+2=1$; both are impossible for natural numbers. Thus an edge must come from the third case. Its lower-bound conditions hold automatically for $u+2$ and $v+2$, and subtracting $2$ from each recovers $u$ and $v$, leaving precisely the step relation. Conversely, the step relation supplies that third edge case, since both shifted vertices are at least $2$.
