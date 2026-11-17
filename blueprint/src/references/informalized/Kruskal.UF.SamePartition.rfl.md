<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.UF.SamePartition.rfl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reflexivity of the same-partition relation

**Claim.** Every union-find state induces the same partition as itself: for any two nodes, their labels agree in the first state if and only if they agree in the second, which here is the same state.

**Proof.** Fix any two nodes $i,j$. The proposition that the state assigns them equal labels is equivalent to itself, in both directions, by reflexivity of logical equivalence. This holds for every pair of nodes, which is precisely the same-partition condition.
