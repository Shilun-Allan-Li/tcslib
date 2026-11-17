<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_graphPartitePerfectMatching_eq_partitePerfectMatching -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of matching counts

**Claim.** For every pair of natural numbers $r$ and $k$, the number of perfect matchings in the complete $2r$-partite graph with $k$ vertices in each part equals the number of perfect matching codes whose decoded pairs lie in distinct parts.

**Proof.** Split into the cases $k=0$ and $k>0$. When $k=0$, both counts are $1$, by the zero-size counting results for graph matchings (`card_graphPartitePerfectMatching_zero`) and matching codes (`card_partitePerfectMatching_zero`). When $k>0$, apply the positive-part-size equality (`card_graphPartitePerfectMatching_eq_partitePerfectMatching_of_pos`).

**Key facts.** `FABL.card_graphPartitePerfectMatching_zero`, `FABL.card_partitePerfectMatching_zero`, `FABL.card_graphPartitePerfectMatching_eq_partitePerfectMatching_of_pos`.
