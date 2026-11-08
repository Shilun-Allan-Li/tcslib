<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordinateDecisionTree.assignCoordinates_eq_on_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values on Queried Coordinates

**Claim.** After assigning the values of $x$ at each coordinate in $L$ to the seed assignment $s$, every coordinate appearing in $L$ has its value from $x$.

**Proof.** Proceed by induction on $L$, allowing the seed assignment to vary. The empty list has no coordinate to check. For a list with first coordinate $j$ and tail $L'$, membership of $i$ means either $i=j$ or $i$ occurs in $L'$. If $i$ occurs in the tail, the induction hypothesis applied after the first update gives the result. Otherwise, in the first-coordinate case, $i=j$ and it does not occur in the tail. The assignment on the tail therefore leaves its value equal to the updated seed's value at $j$, by the fact that assignment leaves coordinates outside the list unchanged (`assignCoordinates_apply_of_not_mem`). The first update set that value to $x_j$, as required.

**Key facts.** `FABL.CoordinateDecisionTree.assignCoordinates_apply_of_not_mem`.
