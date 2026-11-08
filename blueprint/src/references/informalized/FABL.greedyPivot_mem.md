<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.greedyPivot_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivot Membership

**Claim.** The greedy pivot chosen from a largest part slice belongs to the remaining set.

**Proof.** The largest-part slice is nonempty by `greedyLargestPartSlice_nonempty`. Its chosen element therefore belongs to the filtered set defining that slice. Membership in a filtered set implies membership in the original remaining set, which proves the claim.

**Key facts.** `FABL.greedyLargestPartSlice_nonempty`.
