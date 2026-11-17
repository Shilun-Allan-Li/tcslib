<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.clearF₂PivotRows_column_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of a zero column

**Claim.** If the pivot equation and every row have coefficient zero at a fixed variable, then clearing the pivot variable from the rows preserves that zero coefficient.

**Proof.** Take any row in the cleared list. Since the list is formed by mapping the clearing operation over the original rows, it is the clearing of some original row. If that row already has coefficient zero at the pivot variable, clearing leaves it unchanged, so its coefficient at the fixed variable is zero by hypothesis. Otherwise, clearing adds the pivot equation to it. At the fixed variable, the resulting coefficient is the sum of the two original coefficients, both of which are zero. Thus the cleared row still has coefficient zero there.
