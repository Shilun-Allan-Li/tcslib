<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satTransform_equisat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equisatisfiability of the transform

**Claim.** The transformed formula is satisfiable exactly when the original formula is satisfiable.

**Proof.** For the forward implication, take an assignment satisfying the transformed formula. Soundness of the threaded transform (`Complexity.satTransformFrom_sound`), started at the original variable bound, shows that the same assignment satisfies the original formula. For the reverse implication, take an assignment satisfying the original formula. Every literal in the formula has index below its number of variables (`Complexity.sat_literal_lt_numVars`), so the completeness result for the threaded transform applies with that number as cursor. It supplies an assignment satisfying the transformed formula (and agreeing with the original assignment below the cursor). Thus each formula is satisfiable whenever the other is.

**Key facts.** `Complexity.satTransformFrom_sound`, `Complexity.sat_literal_lt_numVars`, `Complexity.satTransformFrom_complete`.
