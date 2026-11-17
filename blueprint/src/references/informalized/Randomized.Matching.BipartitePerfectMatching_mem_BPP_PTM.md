<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.BipartitePerfectMatching_mem_BPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect Matching in Bounded-Error Polynomial Time

**Claim.** The language of encodings of Boolean adjacency matrices whose associated bipartite graph has a perfect matching is decidable in probabilistic polynomial time, with acceptance probability at least $2/3$ on members and at most $1/3$ on nonmembers.

**Proof.** The proof first uses the established result that the perfect-matching language belongs to one-sided polynomial time (Randomized.Matching.BipartitePerfectMatching_mem_RP_PTM). It then applies the inclusion of one-sided polynomial time in bounded-error polynomial time (Randomized.RP_PTM_subset_BPP_PTM), which gives the claimed membership.

**Key facts.** `Randomized.Matching.BipartitePerfectMatching_mem_RP_PTM`, `Randomized.RP_PTM_subset_BPP_PTM`.
