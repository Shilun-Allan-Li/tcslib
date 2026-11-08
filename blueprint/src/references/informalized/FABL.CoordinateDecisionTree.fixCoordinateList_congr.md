<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordinateDecisionTree.fixCoordinateList_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction Depends on Listed Coordinates

**Claim.** If $x$ and $y$ agree at every coordinate in $C$, then fixing the coordinates in $C$ according to either vector produces the same restriction.

**Proof.** Induct on the list $C$, allowing the starting restriction to vary. For the empty list, neither vector changes the restriction. For $C=i::C'$, fixing the first coordinate produces the same intermediate restriction for both vectors because $x_i=y_i$. The remaining vectors still agree at every coordinate in the tail, since each tail coordinate occurs in the full list. The induction hypothesis applied to the common intermediate restriction shows that processing the tail also gives the same result. The decomposition of list fixing into its first update followed by fixing the tail is the list-cons identity (`FABL.CoordRestriction.fixCoordinateList_cons`).

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_cons`.
