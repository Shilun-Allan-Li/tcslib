<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.isSatisfied_setF₂PivotValue_iff_of_coefficient_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivot Update Preserves Other Equations

**Claim.** If the row equation has coefficient $0$ at the pivot variable, then it is satisfied after the pivot update exactly when it was satisfied before the update.

**Proof.** Compare the row’s evaluations before and after the update, coordinate by coordinate. At the pivot coordinate, the row contributes zero both times because its coefficient there is zero. At every other coordinate the update leaves the assignment unchanged. Thus each term, and hence the whole finite sum, is unchanged. The row’s constant is unchanged as well, so equality to that constant holds before the update if and only if it holds afterward.
