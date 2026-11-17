<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.fixCoordinateList_apply_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at a listed coordinate

**Claim.** For a list with no repetitions, the assignment formed by fixing its coordinates according to the signs encoded by $x$ has at every listed coordinate $i$ the fixed state determined by the sign encoded by $x_i$.

**Proof.** Induct on the list, allowing the initial assignment to vary. The empty list has no listed coordinate. For a list with head $i$ and tail $L$, expand the fold into the initial fix at $i$ followed by processing the tail. If the queried coordinate is the head, the absence of repetitions means it is not in the tail. The list-fixing operation on the tail therefore leaves its value unchanged (`fixCoordinateList_apply_of_not_mem`); the preceding fix sets it to the state determined by the sign encoded by $x_i$. If the queried coordinate lies in the tail, the tail remains without repetitions, and the induction hypothesis applied after the head fix gives the claimed state there. The fold decomposition used in both cases is `fixCoordinateList_cons`.

**Key facts.** `FABL.CoordRestriction.fixCoordinateList_cons`, `FABL.CoordRestriction.fixCoordinateList_apply_of_not_mem`.
