<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.CoordRestriction.mem_freeCoordinates_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Free Coordinate Membership

**Claim.** A coordinate belongs to the free coordinate set of a restriction assignment exactly when the assignment marks that coordinate free.

**Proof.** By definition, the free coordinate set consists of those elements of the full coordinate set for which the restriction state is free. Since the given coordinate is already in that full set, membership in the filtered set is equivalent to the filter condition, namely that its state is free.
