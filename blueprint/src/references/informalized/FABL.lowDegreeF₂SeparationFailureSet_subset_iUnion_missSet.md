<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂SeparationFailureSet_subset_iUnion_missSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separation failure lies in a miss set

**Claim.** Every list of inputs that fails to distinguish all low-degree coefficient families lies in the miss set of some nonzero low-degree coefficient family.

**Proof.** The characterization of separation (`separatesLowDegreeF₂Coefficients_iff`) says that separation holds exactly when every nonzero coefficient family has a nonzero polynomial value on at least one sample input. Negating this characterization for a list that fails separation produces a nonzero coefficient family whose polynomial evaluates to zero at every input in the list. That family, together with the all-zero evaluation condition, is exactly a witness that the list belongs to its miss set, so the list lies in the union of those miss sets.

**Key facts.** `FABL.separatesLowDegreeF₂Coefficients_iff`.
