<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordRestrictionOf_freeCoordinates_fixedSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of a coordinate restriction

**Claim.** The restriction obtained by taking the free coordinates of $\rho$ and its fixed signs is exactly $\rho$.

**Proof.** To prove equality of the two restrictions, fix a coordinate $i$ and consider the three possible values of $\rho(i)$. If it is free, then $i$ belongs to the set of free coordinates, by the characterization that membership is equivalent to having value free (`CoordRestriction.mem_freeCoordinates_iff`). The recovered restriction therefore assigns free at $i$. If $\rho(i)$ is fixed to $1$ or to $-1$, that characterization shows that $i$ is outside the free set. The recovered restriction then reads the fixed sign supplied by $\rho$; the definition of the fixed-sign assignment gives respectively $1$ or $-1$, so the recovered restriction agrees with $\rho$ in either case. Since the two restrictions agree at every coordinate, they are equal.

**Key facts.** `FABL.CoordRestriction.mem_freeCoordinates_iff`.
