<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.restrictionAssignmentWeightAt_fixCoordinateList_of_all_fixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight invariance on fixed coordinates

**Claim.** If every coordinate in the distinct list $L$ is already fixed in $\rho$, then fixing those coordinates according to $x$ leaves the assignment weight unchanged.

**Proof.** Compare the products defining the two assignment weights coordinate by coordinate. If a coordinate belongs to $L$, list-fixing makes its state the fixed state specified by the corresponding sign of $x$ (\texttt{CoordRestriction.fixCoordinateList\_apply\_of\_mem}). Either fixed state has the same coordinate weight, $(1-\delta)/2$, and the original state was fixed as well; hence the factor is unchanged. If a coordinate does not belong to $L$, its state is unchanged by list-fixing (\texttt{CoordRestriction.fixCoordinateList\_apply\_of\_not\_mem}), so its factor is unchanged too. Thus all factors, and therefore the products, agree.

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_apply_of_mem`, `FABL.coordRestrictionWeightAt_fixedState`, `FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem`.
