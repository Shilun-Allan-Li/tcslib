<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHard.lean :: Complexity.PathHard.adjWordE_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency word entry

**Claim.** For $k<n^2$, the adjacency word entry at position $k$, with false as the default out of range, is true exactly when there is an edge from vertex $\lfloor k/n\rfloor$ to vertex $k\bmod n$.

**Proof.** The adjacency word is formed by mapping the positions in the range $0,1,\ldots,n^2-1$ to the Boolean decision of whether the corresponding edge exists. Since $k<n^2$, position $k$ is in this range, so the default value in the bounded lookup is not used. The entry returned by the lookup is consequently the mapped value at position $k$, namely the decision of the edge from $\lfloor k/n\rfloor$ to $k\bmod n$.
