<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.fixCoordinateList_free_imp_original_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free Coordinates Remain Free

**Claim.** If coordinate $j$ is free after the listed coordinate updates, then it was free in the original assignment $\rho$.

**Proof.** Split into whether $j$ belongs to the list. If it does, the fact that every listed coordinate is nonfree after the updates (`fixCoordinateList_ne_free_of_mem`) contradicts the assumption that the final state at $j$ is free. Thus $j$ is absent from the list. The updates then leave its state equal to $\rho_j$ (`fixCoordinateList_apply_of_not_mem`), so the assumed final freeness gives $\rho_j=\mathrm{free}$.

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_ne_free_of_mem`, `FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem`.
