<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.eliminateF₂Rows_residual_coefficient_eq_zero_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Residuals Vanish on Processed Coordinates

**Claim.** Every residual equation produced by eliminating along a coordinate list has coefficient zero at each coordinate that occurs in that list.

**Proof.** Induct on the coordinate list, allowing the input rows to vary. There are no coordinates in the empty list, so the assertion is vacuous. For a nonempty list, let its first coordinate be $z$. If the specified coordinate is a later coordinate, apply the induction hypothesis to the recursive elimination, whether or not a pivot is found. If the specified coordinate is $z$ itself and no pivot is found, every input row already has coefficient zero at $z$: this is the characterization of failed pivot extraction (`extractF₂Pivot_eq_none_iff`). The zero-column preservation result (`eliminateF₂Rows_preserves_zero_column`) then gives the claim for the residuals. If a pivot is found instead, its coefficient at $z$ is $1$ (`extractF₂Pivot_coefficient_eq_one`). Clearing it makes every remaining row's coefficient at $z$ equal to zero (`F₂LinearEquation.clearPivot_coefficient_eq_zero`). Applying zero-column preservation to those cleared rows shows that the recursive residuals have zero coefficient at $z$, as required.

**Key facts.** `FABL.extractF₂Pivot_eq_none_iff`, `FABL.eliminateF₂Rows_preserves_zero_column`, `FABL.extractF₂Pivot_coefficient_eq_one`, `FABL.F₂LinearEquation.clearPivot_coefficient_eq_zero`.
