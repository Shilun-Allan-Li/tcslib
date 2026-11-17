<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.eliminateF₂Rows_pivots_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivot Count Bound

**Claim.** Eliminating along a coordinate list produces no more pivots than the length of that list.

**Proof.** Proceed by induction on the coordinate list, allowing the input row list to vary. With no coordinates, elimination returns an empty pivot list, so the bound holds. For a nonempty list, consider its first coordinate. If no pivot row is found, elimination adds no pivot at this stage and recurses on the remaining coordinates with the same rows; the induction hypothesis bounds the resulting pivot count by the number of remaining coordinates. If a pivot row is found, elimination records exactly one pivot and recurses on the remaining coordinates after clearing the other rows. By induction, the recursive pivot list has length at most the number of remaining coordinates, so including the one recorded pivot gives the desired bound.
