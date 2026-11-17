<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.complete_coordRestrictionOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of a Coordinate Restriction

**Claim.** Completing the restriction that leaves $J$ free and fixes its complement according to $z$ gives the sign vector encoded from $x$ on $J$ and equal to $z$ off $J$.

**Proof.** Check equality at each coordinate $i$. When $i\in J$, the restriction is free, so its completion is the sign encoding of $x_i$. The combined sign vector has this same free-coordinate value by `combineSignCube_apply_free`. When $i\notin J$, the restriction fixes the coordinate according to the sign $z_i$, while the combined sign vector has fixed-coordinate value $z_i$ by `combineSignCube_apply_fixed`. Since each sign is either $1$ or $-1$, the definition of the restriction selects the corresponding fixed case. Thus the two vectors agree everywhere.

**Key facts.** `FABL.combineSignCube_apply_free`, `FABL.combineSignCube_apply_fixed`.
