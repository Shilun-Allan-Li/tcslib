<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkCover.lean :: Randomized.RegularMultigraph.coverAdj_symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of lifted adjacency

**Claim.** If $(x,b)$ is joined to $(y,c)$ in the two-sheeted lift, then $(y,c)$ is joined to $(x,b)$.

**Proof.** The given lifted edge supplies a neighbor slot at $x$ leading to $y$, and its labels satisfy $c=\neg b$. By symmetry of multigraph adjacency (`Randomized.RegularMultigraph.adj_symm`), there is a neighbor slot at $y$ leading back to $x$. Also, Boolean negation is involutive, so $b=\neg c$. These facts give the required lifted edge in the reverse direction.

**Key facts.** `Randomized.RegularMultigraph.adj_symm`.
