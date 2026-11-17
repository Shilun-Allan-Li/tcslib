<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.UF.SamePartition.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of Induced Partitions

**Claim.** If the first and second union-find states induce the same partition, and the second and third do as well, then the first and third induce the same partition.

**Proof.** Fix nodes $i,j$. Equality of their representatives in the first state is equivalent, by the first hypothesis, to equality in the second state; by the second hypothesis, this is equivalent to equality in the third. Chaining the two equivalences gives the claimed equivalence.
