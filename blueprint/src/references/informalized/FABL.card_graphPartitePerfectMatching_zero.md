<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_graphPartitePerfectMatching_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching count with empty parts

**Claim.** For every natural number $r$, the complete $2r$-partite graph with zero vertices in each part has exactly one perfect matching.

**Proof.** Every graph perfect matching injects into the set of perfect matchings on the same total number of vertices viewed as a complete graph (`graphPartiteMatchingToCompletePerfectMatching_injective`). Here that total is zero, and the complete-graph matching count is $1$ (`card_completePerfectMatching`). Hence the graph matching count is at most $1$. The empty graph matching supplies at least one such matching, so the count is positive. Since it is a natural number bounded above by $1$ and positive, it equals $1$.

**Key facts.** `FABL.graphPartiteMatchingToCompletePerfectMatching_injective`, `FABL.card_completePerfectMatching`.
