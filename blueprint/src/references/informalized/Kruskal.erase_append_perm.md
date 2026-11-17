<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/GraphTheory/Kruskal/UnionFind.lean :: Kruskal.erase_append_perm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moving a Member to the End

**Claim.** If a weighted edge occurs in a finite list, the list is a permutation of the list formed by removing its first occurrence and appending it at the end.

**Proof.** Because the edge occurs in the list, removing its first occurrence removes one copy of it. The remaining list together with one appended copy therefore has exactly the same elements with the same multiplicities as the original list. Hence the lists are permutations.
