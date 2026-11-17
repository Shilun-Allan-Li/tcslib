<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.coordSwitchingFailureProbability_eq_zero_of_width_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure Probability at Zero Width

**Claim.** If a DNF formula has width zero and $k>0$, then its coordinate-switching failure probability at parameter $\delta$ and threshold $k$ is zero.

**Proof.** Expand the failure probability as a sum over restrictions. For each restriction, its summand is the restriction's weight multiplied by an indicator that equals one only if the restricted function has decision-tree depth at least $k$. Since $k>0$, that event would imply depth at least one. A function has decision-tree depth at least one exactly when it takes different values at some two inputs (`one_le_decisionTreeDepth_iff_nonconstant`). But a width-zero formula defines a constant function: its values agree on every pair of inputs (`DNFFormula.toBooleanFunction_eq_of_width_eq_zero`), and therefore also on the two completions arising from this restriction. The event is impossible, so every indicator and every summand is zero. Thus the full sum is zero.

**Key facts.** `FABL.one_le_decisionTreeDepth_iff_nonconstant`, `FABL.DNFFormula.toBooleanFunction_eq_of_width_eq_zero`.
