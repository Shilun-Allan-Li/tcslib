<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.freeWithin_fixCoordinateList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free Coordinates After Fixing a List

**Claim.** After fixing the coordinates in $L$ according to $x$, every coordinate that remains free belongs to $A\setminus L$, where $L$ is viewed as the set of its entries.

**Proof.** Take a coordinate $j$ that remains free. It cannot belong to $L$, because fixing a listed coordinate gives it a nonfree state. Since $j$ is outside $L$, fixing the list leaves its state unchanged, so $j$ was free under $\rho$ and hence belongs to $A$. Thus it lies in $A$ and outside the set of entries of $L$, as required.

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_ne_free_of_mem`, `FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem`.
