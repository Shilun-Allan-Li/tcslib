<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.UniformRefinement.paddedCloneValue_le_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Padded-clone value is at most its optimum

**Claim.** Every assignment’s padded-clone value is at most the optimum padded-clone value.

**Proof.** The padded-clone value is a function on the finite set of assignments. Its maximum is attained, and the padded-clone optimum is defined to be its value at a maximizing assignment. By the defining property of a maximum, the value at any given assignment is no larger than that maximum.
