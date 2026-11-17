<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.restrictionAssignmentWeightAt_fixCoordinateList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight change under coordinate fixing

**Claim.** If the distinct coordinates in $L$ are all free in $\rho$, then the weight of $\rho$ is the weight after fixing them according to $x$, multiplied by $\bigl(2\delta/(1-\delta)\bigr)^{|L|}$.

**Proof.** Proceed by induction on the list $L$, with the initial assignment allowed to vary. For the empty list, no coordinate changes and the multiplicative factor is $1$. For the inductive step, write $L=i::L'$. First fix coordinate $i$ according to the sign encoded by $x_i$, obtaining an assignment $\eta$. Since the list has no repetitions, $i$ is not in $L'$. Fixing $i$ leaves every coordinate of $L'$ unchanged, so they remain free. The one-coordinate weight-change formula (\texttt{restrictionAssignmentWeightAt\_fixCoordinate}) therefore gives that the original weight is the switching ratio times the weight of $\eta$. Apply the induction hypothesis to $\eta$ and $L'$. Finally, the list-fixing operation first fixes $i$ and then processes $L'$ (\texttt{CoordRestriction.fixCoordinateList\_cons}); the list length increases by one, so the resulting factors combine to the required power.

**Key facts.** `FABL.restrictionAssignmentWeightAt_fixCoordinate`, `FABL.CoordRestriction.fixCoordinate_apply_of_ne`, `FABL.CoordRestriction.fixCoordinateList_cons`.
