<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordSwitchingFailureIndicator_coordRestrictionOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching Failure for Fixed Coordinates

**Claim.** The switching failure indicator under the assignment that leaves $J$ free and fixes the other coordinates to $z$ equals the indicator for the function obtained by fixing those outside coordinates to $z$.

**Proof.** The restriction of the original function under the assignment that leaves $J$ free and fixes the other coordinates to $z$ is exactly the restricted function obtained by fixing those coordinates (\texttt{FABL.restrict_coordRestrictionOf}). Consequently their decision-tree depths agree. The indicators compare each depth with the same threshold $k$, so they are equal.

**Key facts.** `FABL.restrict_coordRestrictionOf`.
