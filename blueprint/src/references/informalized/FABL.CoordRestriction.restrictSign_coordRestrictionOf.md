<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CoordRestriction.restrictSign_coordRestrictionOf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction from Fixed Coordinates

**Claim.** Restricting according to the coordinate states determined by $J$ and $z$ is the same as evaluating on the cube point formed by combining the free coordinates with $z$.

**Proof.** Evaluate the two functions at an arbitrary input $x$. By the definitions of restriction and extended restriction, the left side evaluates $f$ at the completion of $x$ using the states determined by $J$ and $z$, while the right side evaluates $f$ at the point combining the coordinates of $x$ in $J$ with $z$ outside $J$. These inputs agree by the completion identity for a restriction built from $J$ and $z$ (`completeSign_coordRestrictionOf`). Therefore the function values agree at every input.

**Key facts.** `FABL.CoordRestriction.completeSign_coordRestrictionOf`.
