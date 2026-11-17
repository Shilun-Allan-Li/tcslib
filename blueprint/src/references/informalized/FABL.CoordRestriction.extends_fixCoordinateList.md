<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.extends_fixCoordinateList -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extension after list fixing

**Claim.** If every coordinate in a list is free in the original restriction, then fixing the list according to the signs encoded by $x$ agrees with the original restriction at every coordinate where that restriction was not free.

**Proof.** Take any coordinate $i$ whose original state is not free. It cannot belong to the list, because every listed coordinate is free by hypothesis. A coordinate outside the list is unchanged by the list of fixes (`fixCoordinateList_apply_of_not_mem`), so the resulting assignment at $i$ equals the original one. This is precisely the required extension property.

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem`.
