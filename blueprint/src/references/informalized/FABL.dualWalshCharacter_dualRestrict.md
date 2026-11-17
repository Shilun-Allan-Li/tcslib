<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.dualWalshCharacter_dualRestrict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction of Walsh characters

**Claim.** Restricting a linear functional to a subspace gives a Walsh character whose value at any subspace element equals the original Walsh character evaluated at that element in the ambient space.

**Proof.** Both sides are obtained by applying the same binary sign character to the same scalar: restriction evaluates the functional at the subspace element, which is its ambient value. Thus the two expressions agree by unfolding the definitions.
