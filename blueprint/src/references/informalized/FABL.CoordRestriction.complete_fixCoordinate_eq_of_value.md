<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.CoordRestriction.complete_fixCoordinate_eq_of_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion after fixing to its value

**Claim.** If the completion under a restriction has value $s$ at coordinate $i$, then fixing coordinate $i$ to $s$ leaves the entire completed sign vector unchanged.

**Proof.** Compare the two completed vectors coordinate by coordinate. At any coordinate $j\ne i$, the update fixing $i$ does not alter the restriction at $j$, so the completed values agree. At $i$, the hypothesis says the original completed value is $s$. Since a sign is either $1$ or $-1$, fixing the coordinate to $s$ gives precisely that same value. Thus the vectors agree at every coordinate.
