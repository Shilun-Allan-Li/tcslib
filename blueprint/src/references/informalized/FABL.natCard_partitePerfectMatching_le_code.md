<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.natCard_partitePerfectMatching_le_code -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partite matching code count bound

**Claim.** For natural numbers $q$ and $k$, the number of partite perfect matching codes is at most the number of perfect matching codes with parameter $(qk)/2$.

**Proof.** A partite perfect matching code is, by definition, a perfect matching code equipped with the property that its decoded edges meet the partite condition. Forgetting that property sends each such object to its underlying code, and this map is injective: two subtype elements with the same underlying code are equal. Hence the number of partite codes is no greater than the number of all codes.
