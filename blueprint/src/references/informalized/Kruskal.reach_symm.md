<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/Reach.lean :: Kruskal.reach_symm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of reachability

**Claim.** If one vertex is reachable from another through a given edge list, then the reverse reachability also holds.

**Proof.** Induct on the path. The reflexive path is symmetric. For an extended path, first traverse the last adjacency in reverse, which is valid by symmetry of symmetric adjacency (`symAdj_symm`), and then follow the induction hypothesis to reverse the earlier part. Concatenating these paths gives the reversed reachability.

**Key facts.** `Kruskal.symAdj_symm`.
