<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.flattenPairList_decodePerfectMatchingCode_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct decoded endpoints

**Claim.** If the vertex list has length $2m$ and no repetitions, then the list of endpoints obtained by decoding a perfect-matching code also has no repetitions.

**Proof.** The decoded endpoint list is a permutation of the original vertex list by the permutation theorem (`flattenPairList_decodePerfectMatchingCode_perm`). A list permutation preserves the property of having no repetitions, so the endpoint list is nodup.

**Key facts.** `FABL.flattenPairList_decodePerfectMatchingCode_perm`.
