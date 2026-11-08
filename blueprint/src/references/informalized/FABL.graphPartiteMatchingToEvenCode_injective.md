<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphPartiteMatchingToEvenCode_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Even-Partite Code Map

**Claim.** For $k>0$, the map sending a perfect matching in the complete multipartite graph with $2r$ parts of size $k$ to its even-partite perfect-matching code is injective.

**Proof.** Suppose two matchings have the same even-partite code. Equality of these subtype codes implies equality of their underlying raw codes. Applying injectivity of the inverse matching-code equivalence shows that the corresponding complete-graph matchings are equal. The relabeling map is injective (`graphPartiteMatchingToCompletePerfectMatching_injective`), so the original partite matchings are equal.

**Key facts.** `FABL.graphPartiteMatchingToCompletePerfectMatching_injective`.
