<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.mergeAll_cons_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading edge in a merge fold

**Claim.** Folding $e :: S$ into a union-find state and folding $S$ into the state obtained by first merging the endpoints of $e$ give the same partition.

**Proof.** By the recursive definition of the merge fold, both expressions are the same union-find state: each first merges the endpoints of $e$ into $uf$, then folds the remaining list $S$. Every state induces the same partition as itself (`UF.SamePartition.rfl`), so the claimed partition equivalence follows.

**Key facts.** `Kruskal.UF.SamePartition.rfl`.
