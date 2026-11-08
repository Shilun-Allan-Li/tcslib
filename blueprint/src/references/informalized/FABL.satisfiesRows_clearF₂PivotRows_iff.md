<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.satisfiesRows_clearF₂PivotRows_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivot Clearing Preserves Satisfaction

**Claim.** For an assignment satisfying a pivot equation, clearing its chosen coefficient from every row preserves satisfaction of the list of equations.

**Proof.** Clearing the pivot maps each row to its cleared row, so a row in the resulting list comes from an original row. For the fixed assignment, the pivot-clearing identity says that the cleared row is satisfied exactly when the original row is satisfied, provided the pivot itself is satisfied (`FABL.F₂LinearEquation.isSatisfied_clearPivot_iff`). Applying this identity to each row gives each implication between satisfaction of all cleared rows and satisfaction of all original rows.

**Key facts.** `FABL.F₂LinearEquation.isSatisfied_clearPivot_iff`.
