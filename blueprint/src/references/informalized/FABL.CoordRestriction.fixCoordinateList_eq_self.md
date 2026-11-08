<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.fixCoordinateList_eq_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Already Matched Restrictions Are Unchanged

**Claim.** If $\eta$ already has the fixed state prescribed by $x$ at every coordinate in $L$, then fixing the coordinates in $L$ according to $x$ leaves the entire assignment $\eta$ unchanged.

**Proof.** Induct on the list, allowing the assignment to vary. The empty list makes no changes. For a list with first coordinate $i$ and tail $L'$, split the update using `fixCoordinateList_cons`. The hypothesis gives that $\eta_i$ is already the prescribed fixed state, so the first update at $i$ leaves the whole assignment unchanged: at $i$ it writes the value already present, and at every other coordinate it preserves the value (`fixCoordinate_apply_of_ne`). The hypothesis also holds on the tail, since every coordinate in $L'$ is in the original list. The induction hypothesis then shows that processing the tail leaves $\eta$ unchanged as well.

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_cons`, `FABL.CoordRestriction.fixCoordinate_apply_of_ne`.
