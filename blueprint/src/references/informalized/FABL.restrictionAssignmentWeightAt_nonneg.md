<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.restrictionAssignmentWeightAt_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of assignment weight

**Claim.** If $0\leq\delta\leq1$, then the assignment weight is nonnegative for every restriction assignment.

**Proof.** Under the stated bounds, the coordinate weight of each state is nonnegative: it is $\delta$ for a free state and $(1-\delta)/2$ for either fixed state (\texttt{coordRestrictionWeightAt\_nonneg}). The assignment weight is the finite product of these coordinate weights, which is nonnegative.

**Key facts.** `FABL.coordRestrictionWeightAt_nonneg`.
