<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.fixCoordinateList_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Coordinate of a List Update

**Claim.** Fixing the coordinates in the list consisting of $i$ followed by $L$ according to $x$ is equivalent to first fixing $i$ according to the sign encoded by $x_i$, then fixing the coordinates in $L$ according to $x$.

**Proof.** The list update is defined by folding successive coordinate updates from left to right. Splitting off the first entry $i$ therefore gives exactly the update at $i$ followed by the fold over the remaining list; this is a definitional equality.
