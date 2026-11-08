<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordSwitchingFailureProbability_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure Probability Upper Bound

**Claim.** If $0\le\delta\le1$, then the coordinate-switching failure probability is at most $1$.

**Proof.** For each coordinate restriction, its assignment weight is nonnegative (\texttt{restrictionAssignmentWeightAt\_nonneg}), and its failure indicator is either $0$ or $1$, hence at most $1$. Multiplying these inequalities shows that each weighted failure contribution is at most its assignment weight. Summing over all restrictions bounds the failure probability by the total assignment weight, which equals $1$ (\texttt{sum\_restrictionAssignmentWeightAt}).

**Key facts.** `FABL.restrictionAssignmentWeightAt_nonneg`, `FABL.sum_restrictionAssignmentWeightAt`.
