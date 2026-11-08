<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_completePerfectMatching -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count of Complete Perfect Matchings

**Claim.** For every natural number $m$, the complete graph on $2m$ vertices has $(2m-1)!!$ perfect matchings, with the count given by the natural-number double factorial in this formula.

**Proof.** The proof bounds the number of complete-graph perfect matchings in both directions. First, each perfect-matching code determines a complete-graph perfect matching, and this map is injective (`FABL.perfectMatchingGraphOfCode_injective`). Hence the number of complete-graph matchings is at least the number of codes. The codes have cardinality $(2m-1)!!$ (`FABL.natCard_perfectMatchingCode`). Conversely, every complete-graph perfect matching injects into the set of pairing permutations (`FABL.completePerfectMatchingToPairingPerm_injective`), whose cardinality is $(2m-1)!!$ (`FABL.card_pairingPerm`). The two bounds coincide, proving the formula.

**Key facts.** `FABL.perfectMatchingGraphOfCode_injective`, `FABL.natCard_perfectMatchingCode`, `FABL.completePerfectMatchingToPairingPerm_injective`, `FABL.card_pairingPerm`.
