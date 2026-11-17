<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.completePerfectMatchingToPairingPerm_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the matching map

**Claim.** For every $m$, the map sending a perfect matching on $2m$ vertices to its partner permutation is injective.

**Proof.** Take two perfect matchings whose associated pairing permutations agree as permutations. Since each matching is recovered from its partner permutation, equality of these permutations implies equality of the matchings. This is exactly the injectivity of the matching-to-permutation map; the subtype equality in the hypothesis supplies equality of the underlying permutations.

**Key facts.** `FABL.perfectMatchingPartnerPerm_injective`.
