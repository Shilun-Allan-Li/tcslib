<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unlisted Coordinates Are Unchanged

**Claim.** If coordinate $j$ is not in the list $L$, fixing the coordinates in $L$ according to $x$ leaves the state at $j$ equal to its original value $\rho_j$.

**Proof.** Induct on the list, allowing the initial assignment $\rho$ to vary. The empty list performs no updates, so the claim holds immediately. For a list with first coordinate $i$ and tail $L'$, nonmembership of $j$ means both $j\ne i$ and $j\notin L'$. By the list decomposition (`fixCoordinateList_cons`), first update $i$ and then process $L'$. The induction hypothesis applied to the updated assignment says that processing $L'$ leaves its value at $j$ unchanged. Since $j\ne i$, updating coordinate $i$ itself leaves the value at $j$ equal to $\rho_j$ (`fixCoordinate_apply_of_ne`).

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_cons`, `FABL.CoordRestriction.fixCoordinate_apply_of_ne`.
