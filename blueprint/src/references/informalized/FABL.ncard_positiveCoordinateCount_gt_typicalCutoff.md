<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.ncard_positiveCoordinateCount_gt_typicalCutoff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting vectors above the cutoff

**Claim.** For the specified cutoff, the number of sign vectors with more positive coordinates than the cutoff equals the number of subsets of the coordinate set with cardinality greater than the cutoff.

**Proof.** Map each sign vector to the subset of coordinates where it equals $1$; this is the bijection `signCubeEquivFinset`. The cardinality of that subset is exactly the positive-coordinate count (`signCubeEquivFinset_apply_card`), so the map sends vectors satisfying the strict cutoff inequality to subsets satisfying the corresponding cardinality inequality. Because the map is injective, and every subset has a preimage under its inverse, it restricts to a bijection between these two sets. Their finite cardinalities are therefore equal.

**Key facts.** `FABL.signCubeEquivFinset_apply_card`.
