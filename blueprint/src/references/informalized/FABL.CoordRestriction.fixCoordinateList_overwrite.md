<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.fixCoordinateList_overwrite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated Updates Are Overwritten

**Claim.** For a list of distinct coordinates, applying updates prescribed by $x$ and then by $y$ on that list has the same result as applying only the updates prescribed by $y$.

**Proof.** Compare the two assignments coordinate by coordinate. If a coordinate belongs to the list, the distinctness assumption ensures that its final state after processing the list is the fixed state prescribed by the corresponding vector. Thus both procedures give the state prescribed by $y$ there (`fixCoordinateList_apply_of_mem`). If the coordinate is outside the list, neither sequence changes it, so both procedures retain its original state (`fixCoordinateList_apply_of_not_mem`). The assignments therefore agree everywhere.

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_apply_of_mem`, `FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem`.
