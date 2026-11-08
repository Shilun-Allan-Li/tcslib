<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CoordRestriction.completeSign_coordRestrictionOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion from fixed signs

**Claim.** Completing the restriction that leaves coordinates in $J$ free and fixes every coordinate outside $J$ according to $z$, using $x$, gives the sign vector assembled from $x$ on $J$ and $z$ outside $J$.

**Proof.** Prove equality of the two sign vectors coordinatewise. If $i\in J$, the assembled vector takes its free-coordinate value, namely $x(i)$; the restriction is free at $i$, so completion also takes $x(i)$. If $i\notin J$, the assembled vector takes the fixed-coordinate value $z(i)$. The restriction fixes this coordinate according to whether $z(i)=1$ or $z(i)=-1$, and completion returns precisely that fixed sign. These two cases establish equality at every coordinate.

**Key facts.** `FABL.combineSignCube_apply_free`, `FABL.combineSignCube_apply_fixed`.
