<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.extendedSignRestriction_setCoordinate_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Outside the Free Coordinates

**Claim.** If $i$ lies outside $J$, changing coordinate $i$ of the input does not change the extended sign restriction.

**Proof.** Evaluate the two restricted sign vectors coordinate by coordinate. At a coordinate $k\in J$, we have $k\ne i$, since $i\notin J$; thus changing coordinate $i$ leaves the input at $k$ unchanged. The combined vectors therefore agree at every free coordinate. At a coordinate outside $J$, both combined vectors take their value from the fixed assignment $z$, regardless of the input. Hence the combined vectors agree everywhere, and applying $f$ gives the claimed equality. Here we use the coordinate formulas for combining a free and fixed assignment: on free coordinates it returns the free assignment (\texttt{combineSignCube_apply_free}), and on fixed coordinates it returns the fixed assignment (\texttt{combineSignCube_apply_fixed}).

**Key facts.** `FABL.combineSignCube_apply_free`, `FABL.combineSignCube_apply_fixed`.
