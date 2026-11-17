<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.eliminateF₂Rows_preserves_zero_column -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of a Zero Column

**Claim.** If every input equation has coefficient zero at a fixed coordinate, then every pivot equation and residual equation produced by elimination also has coefficient zero there.

**Proof.** Induct on the list of coordinates being processed, with the input rows arbitrary. If the coordinate list is empty, there are no pivots and the residual is the original row list, so the claim is the hypothesis. For a nonempty list, first consider whether a pivot is found. If none is found, every input row remains zero in the fixed column, and the induction hypothesis gives the result for the recursive elimination. If a pivot is found, the extraction preserves the property that all rows, including the pivot and the remaining rows, have zero coefficient in the fixed column (`extractF₂Pivot_forall_iff`). Clearing the pivot rows preserves that zero column (`clearF₂PivotRows_column_eq_zero`). The induction hypothesis therefore gives the property for all pivots and residual rows of the recursive result. The current pivot is also zero in the fixed column, so adjoining it to the recursive pivots completes the proof.

**Key facts.** `FABL.extractF₂Pivot_forall_iff`, `FABL.clearF₂PivotRows_column_eq_zero`.
