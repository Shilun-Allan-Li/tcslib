<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.freeCoordinateList_fixCoordinateList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free Coordinates After Fixing a List

**Claim.** If every coordinate in $L$ is free under $\rho$, then fixing the coordinates in $L$ according to $x$ and making all coordinates in $L$ free again yields exactly $\rho$.

**Proof.** Compare the two assignments at each coordinate $i$. If $i$ belongs to $L$, making the listed coordinates free sets the modified assignment to free there, which agrees with $\rho(i)$ by the hypothesis. If $i$ is outside $L$, fixing the list leaves its state unchanged, and making the list free also leaves its state unchanged. In either case the assignments agree at $i$, so they are equal.

**Key facts.** `FABL.CoordRestriction.freeCoordinateList_apply_of_mem`, `FABL.CoordRestriction.freeCoordinateList_apply_of_not_mem`, `FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem`.
