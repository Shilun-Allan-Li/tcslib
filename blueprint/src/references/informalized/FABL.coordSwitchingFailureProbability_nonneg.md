<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordSwitchingFailureProbability_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of Failure Probability

**Claim.** If $0\le\delta\le1$, then the coordinate-switching failure probability is nonnegative.

**Proof.** The probability is a finite sum over coordinate restrictions. For each restriction, the assignment weight is nonnegative (\texttt{restrictionAssignmentWeightAt\_nonneg}), and the failure indicator is nonnegative (\texttt{coordSwitchingFailureIndicator\_nonneg}). Each product, and therefore their sum, is nonnegative.

**Key facts.** `FABL.restrictionAssignmentWeightAt_nonneg`, `FABL.coordSwitchingFailureIndicator_nonneg`.
