<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.perfectMatchingGraphOfCode_bijective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect Matching Code Bijection

**Claim.** For every natural number $m$, the map that decodes a perfect matching code into a perfect matching of the complete graph on $2m$ vertices is a bijection.

**Proof.** For a map between finite types, bijectivity is equivalent to injectivity together with equality of the two cardinalities. The decoding map is injective (`perfectMatchingGraphOfCode_injective`). Its domain, the type of perfect matching codes, has cardinality $(2m-1)!!$ (`natCard_perfectMatchingCode`), and its codomain, the perfect matchings on the complete graph, has the same cardinality (`card_completePerfectMatching`). Thus the map is bijective.

**Key facts.** `FABL.perfectMatchingGraphOfCode_injective`, `FABL.card_completePerfectMatching`, `FABL.natCard_perfectMatchingCode`.
