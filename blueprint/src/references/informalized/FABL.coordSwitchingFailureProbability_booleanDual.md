<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordSwitchingFailureProbability_booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Duality Preserves Failure Probability

**Claim.** The coordinate-switching failure probability at parameter $\delta$ and threshold $k$ is unchanged when the function is replaced by its Boolean dual.

**Proof.** Expand the probability as a finite sum over coordinate assignments. For each assignment $\rho$, its weight is unchanged when the assignment is negated (\texttt{FABL.restrictionAssignmentWeightAt_negateAssignment}), and the Boolean-dual identity replaces the dual's failure indicator at $\rho$ by the original function's indicator at the negated assignment (\texttt{FABL.coordSwitchingFailureIndicator_booleanDual}). Thus the sum becomes the sum of the original weights times the original indicators, evaluated at negated assignments. Negation is a bijection on the set of assignments, so reindexing the finite sum gives exactly the original failure probability.

**Key facts.** `FABL.restrictionAssignmentWeightAt_negateAssignment`, `FABL.coordSwitchingFailureIndicator_booleanDual`.
