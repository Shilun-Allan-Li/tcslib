<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Reach.lean :: Kruskal.symAdj_symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of symmetric adjacency

**Claim.** If $u$ and $v$ are symmetrically adjacent in an edge list, then $v$ and $u$ are symmetrically adjacent in that list.

**Proof.** Choose an edge witnessing adjacency. If its endpoints are $u,v$ in that order, they are $v,u$ in the reversed order; if they are $v,u$ already, they are $u,v$ after reversal. The same edge remains in the list, so it witnesses the reversed adjacency.
