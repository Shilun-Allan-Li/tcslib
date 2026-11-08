<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.expectRandomRestriction_eq_sum_assignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment-sum formula for restrictions

**Claim.** The random restriction expectation of a function is the sum over all coordinate assignments of its value multiplied by the product of the coordinate weights.

**Proof.** Expand each uniform expectation over the fixed signs as a finite sum divided by the number of sign assignments. Distribute that normalization and the subset weight into each summand. Regard a pair consisting of a free-coordinate set and a sign assignment on its complement as one restriction atom; summing over all such pairs is the same as summing over restriction atoms. The bijection between these atoms and coordinate-by-coordinate assignments identifies each atom with the assignment obtained by leaving the coordinates in the subset free and recording the other signs. Finally, the weight of that assignment is exactly the subset weight divided by the number of fixed-sign assignments (the weight identity `restrictionAssignmentWeightAt_coordRestrictionOf_eq_div`). Reindexing the finite sum by this bijection gives the formula.

**Key facts.** `FABL.restrictionAssignmentWeightAt_coordRestrictionOf_eq_div`.
