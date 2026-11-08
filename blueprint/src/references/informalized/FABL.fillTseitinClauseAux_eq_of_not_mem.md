<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.fillTseitinClauseAux_eq_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unaffected Coordinates in Clause Filling

**Claim.** If a coordinate does not occur among the auxiliary literals, recursive clause filling leaves the assignment unchanged at that coordinate.

**Proof.** Proceed by matching the possible list shapes. When there are at least four clause literals and an auxiliary literal, the operation updates the assignment only at the auxiliary literal's index, then recurses on the modified clause and the remaining auxiliaries. The given coordinate is not the first auxiliary index, since it does not occur in the auxiliary list; it also remains absent from the remaining auxiliary indices. By induction the recursive result agrees with the updated assignment at this coordinate, and because the update was at a different coordinate, that value is the original assignment there. In all other cases the recursion stops and returns the assignment unchanged, so the claim follows directly.
