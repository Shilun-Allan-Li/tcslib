<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.coordSwitchingFailureProbability_le_ratio_pow_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching Failure Probability Bound

**Claim.** For a DNF formula of width at most $w$, the coordinate-switching failure probability at threshold $k+1$ is at most the switching atom ratio raised to $k+1$, multiplied by the number of switching codes of size parameter $k+1$.

**Proof.** Rewrite the failure probability as the total restriction weight over the restrictions that are bad at threshold $k+1` (`DNFFormula.sum_switchingBadWeight_eq_coordSwitchingFailureProbability`). For each such bad restriction, its switching trace has a target restriction. The trace weight identity (`SwitchingTrace.restrictionAssignmentWeightAt_eq_ratio_pow_target`) expresses the original restriction's weight as the target's weight times the switching atom ratio to the power $k+1$. Summing these identities factors out that common power. The remaining sum of target weights is at most the number of switching codes, by `DNFFormula.sum_switchingTraceTargetWeight_le_card` and the width bound. Finally, the atom ratio is nonnegative (`switchingAtomRatio_nonneg`), so multiplying that sum bound preserves the inequality.

**Key facts.** `FABL.DNFFormula.sum_switchingBadWeight_eq_coordSwitchingFailureProbability`, `FABL.DNFFormula.SwitchingTrace.restrictionAssignmentWeightAt_eq_ratio_pow_target`, `FABL.DNFFormula.sum_switchingTraceTargetWeight_le_card`, `FABL.switchingAtomRatio_nonneg`.

**Caveat.** The supplied prose describes a different Håstad switching-lemma statement. This account follows the formal statement and proof source, which establish the switching-code bound.
