<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdInfluence.lean :: FABL.affineLinearForm_setCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Form After Setting a Coordinate

**Claim.** Setting coordinate $i$ of a sign vector to $s$ makes the affine form equal to the remainder omitting $i$, plus the term $a_i s$.

**Proof.** Expand the linear form as a sum over all coordinates, and separate the term at $i$ from the sum over the remaining coordinates. For every other coordinate, setting coordinate $i$ leaves its value unchanged (`FABL.setCoordinate_apply_of_ne`); at coordinate $i$, the updated vector has value $s$ (`FABL.setCoordinate_apply_self`). The separated sum is therefore the affine remainder plus $a_i$ times the real value of $s$, as claimed.

**Key facts.** `FABL.setCoordinate_apply_of_ne`, `FABL.setCoordinate_apply_self`.
