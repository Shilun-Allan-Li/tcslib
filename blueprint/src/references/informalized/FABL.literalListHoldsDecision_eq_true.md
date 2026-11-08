<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.literalListHoldsDecision_eq_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Decision for a List of Literals

**Claim.** The Boolean test for whether at least one literal in a finite list holds returns true exactly when some literal in the list holds under the assignment.

**Proof.** The test applies the Boolean decision procedure for equality of signs to each literal and takes the disjunction over the list. A disjunction is true exactly when one of its entries is true, and equality's decision procedure returns true exactly when the two signs are equal. Thus the test returns true precisely when some listed literal holds.
