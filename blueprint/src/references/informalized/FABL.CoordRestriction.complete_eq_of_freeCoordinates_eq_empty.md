<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.complete_eq_of_freeCoordinates_eq_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion with no free coordinates

**Claim.** If ρ has no free coordinates, completing it with any two binary vectors $x$ and $y$ produces the same sign vector.

**Proof.** It suffices to check each coordinate. No coordinate can be free: if $\rho(i)$ were free, the characterization of membership in the free-coordinate set (FABL.CoordRestriction.mem_freeCoordinates_iff) would put $i$ in that set, contradicting that the set is empty. Hence each coordinate is fixed, either at $1$ or at $-1$. Completion returns that fixed sign regardless of the input vector, so the completions using $x$ and $y$ agree everywhere.

**Key facts.** `FABL.CoordRestriction.mem_freeCoordinates_iff`.
