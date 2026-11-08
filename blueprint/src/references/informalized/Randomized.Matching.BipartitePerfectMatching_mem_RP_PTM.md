<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.BipartitePerfectMatching_mem_RP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect Matching in One-Sided Polynomial Time

**Claim.** The language of encodings of Boolean adjacency matrices whose associated bipartite graph has a perfect matching is decidable in one-sided polynomial time, accepting members with probability at least $2/3$ and rejecting nonmembers on every computation branch.

**Proof.** Use the characterization of membership in one-sided polynomial time by the corresponding machine property (Randomized.mem_RP_PTM_iff). The established result that this language satisfies that machine property (Randomized.Matching.inRP_BipartitePerfectMatching) therefore places it in $\mathrm{RP\_PTM}$.

**Key facts.** `Randomized.mem_RP_PTM_iff`, `Randomized.Matching.inRP_BipartitePerfectMatching`.
