<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.RegularMultigraph.adj_symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of multigraph adjacency

**Claim.** If $u$ is adjacent to $v$ in the regular multigraph, then $v$ is adjacent to $u$.

**Proof.** Choose a neighbor slot at $u$ that leads to $v$. Consequently, the number of slots at $u$ leading to $v$ is positive. The multigraph's multiplicity symmetry says that this number equals the number of slots at $v$ leading to $u$; that latter number is therefore positive as well. Choosing one such slot proves that $v$ is adjacent to $u$.
