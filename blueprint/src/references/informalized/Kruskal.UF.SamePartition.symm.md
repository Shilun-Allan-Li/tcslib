<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.UF.SamePartition.symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of Induced Partitions

**Claim.** If two union-find states induce the same partition, then they induce the same partition in the reverse order.

**Proof.** Fix nodes $i,j$. The hypothesis gives an equivalence between equality of their representatives in the first state and equality in the second. Reversing this equivalence proves the required statement for the states in the opposite order.
