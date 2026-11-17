<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.greedyPivot_part -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivot Part Identity

**Claim.** The greedy pivot chosen from a largest part slice lies in that part.

**Proof.** By `greedyLargestPartSlice_nonempty`, the slice for the greedily chosen part is nonempty. The pivot is chosen from this slice, so it satisfies the slice's defining filter condition: its part coordinate equals the greedily chosen part.

**Key facts.** `FABL.greedyLargestPartSlice_nonempty`.
