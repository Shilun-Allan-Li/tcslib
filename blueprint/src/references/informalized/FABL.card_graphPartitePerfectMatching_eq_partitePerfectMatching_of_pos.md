<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_graphPartitePerfectMatching_eq_partitePerfectMatching_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching count for positive part size

**Claim.** If $k>0$, the number of perfect matchings in the complete $2r$-partite graph with $k$ vertices in each part equals the number of matching codes whose decoded pairs lie in distinct parts.

**Proof.** Because the total number $(2r)k$ of vertices is even, we can compare the two counts through the finite set of even partite perfect matchings. Injectively sending each valid code to its graph matching shows that the code count is at most the graph matching count (`partiteMatchingGraphOfCode_injective`). Injectively encoding each graph matching as an even partite code shows that the graph matching count is at most the even partite matching count (`graphPartiteMatchingToEvenCode_injective`). The valid-code count equals the even partite matching count by the stated equivalence (`partitePerfectMatchingEvenEquiv`). Thus each count is at most the other, so they are equal.

**Key facts.** `FABL.partiteMatchingGraphOfCode_injective`, `FABL.graphPartiteMatchingToEvenCode_injective`.
