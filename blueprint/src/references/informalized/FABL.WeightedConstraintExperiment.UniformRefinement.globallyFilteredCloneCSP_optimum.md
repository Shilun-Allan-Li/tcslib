<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.UniformRefinement.globallyFilteredCloneCSP_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimum after removing isolated variables

**Claim.** The optimum of the globally filtered clone CSP, obtained by restricting the raw instance to variables that appear in constraint scopes, equals the optimum of that raw instance.

**Proof.** The globally filtered clone CSP is defined as the raw CSP instance with isolated variables removed. Apply the theorem that removing isolated variables preserves the optimum (`FABL.RawCSPInstance.optimum_removeIsolatedVariables`) to this raw instance.

**Key facts.** `FABL.RawCSPInstance.optimum_removeIsolatedVariables`.
