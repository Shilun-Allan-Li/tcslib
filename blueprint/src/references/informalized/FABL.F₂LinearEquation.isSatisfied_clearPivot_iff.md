<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.F₂LinearEquation.isSatisfied_clearPivot_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing a Pivot Preserves Satisfaction

**Claim.** If an assignment satisfies the pivot equation, then it satisfies the equation obtained by clearing the pivot from the row exactly when it satisfies the original row.

**Proof.** If the row’s coefficient at the pivot variable is zero, clearing leaves the row unchanged, so the two satisfaction conditions are identical. Otherwise, clearing adds the pivot equation to the row. Since the assignment satisfies the pivot equation, adding it does not change whether the row is satisfied: the fact that adding a satisfied equation preserves satisfaction in both directions is `isSatisfied_add_iff_of_isSatisfied_right`.

**Key facts.** `FABL.F₂LinearEquation.isSatisfied_add_iff_of_isSatisfied_right`.
