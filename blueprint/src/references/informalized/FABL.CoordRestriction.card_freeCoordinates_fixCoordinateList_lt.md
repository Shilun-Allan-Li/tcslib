<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.card_freeCoordinates_fixCoordinateList_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free coordinates decrease after fixing

**Claim.** If a nonempty list consists entirely of coordinates free in ρ, then fixing those coordinates according to $x$ strictly decreases the number of free coordinates.

**Proof.** Write the nonempty list as $i$ followed by a tail. The coordinate $i$ is initially free, so it belongs to the finite set of free coordinates. After fixing the list, no coordinate in the list is free, by the fact that list fixing makes every listed coordinate fixed (FABL.CoordRestriction.fixCoordinateList_ne_free_of_mem). In particular, $i$ has been removed from the free-coordinate set. Moreover, any coordinate still free after fixing cannot occur in the list; for such a coordinate, fixing leaves its state unchanged (FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem), so it was free originally. Thus the new free-coordinate set is contained in the original one with $i$ removed. Removing an element from a finite set strictly lowers its cardinality, yielding the claimed strict inequality. The membership characterization of free coordinates (FABL.CoordRestriction.mem_freeCoordinates_iff) identifies these sets with the stated restrictions.

**Key facts.** `FABL.CoordRestriction.mem_freeCoordinates_iff`, `FABL.CoordRestriction.fixCoordinateList_ne_free_of_mem`, `FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem`.
