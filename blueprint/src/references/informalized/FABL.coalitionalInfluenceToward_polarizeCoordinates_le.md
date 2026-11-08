<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluenceToward_polarizeCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Under Coordinate Polarization

**Claim.** Successive coordinate polarizations do not increase the coalitional influence toward any target sign.

**Proof.** Induct on the list of coordinates, allowing the starting function to vary in the induction hypothesis. For the empty list, polarization leaves the function unchanged, so the influences are equal. For a list beginning with coordinate $i$, the polarized function is obtained by first polarizing $f$ at $i$ and then applying the remaining list (`polarizeCoordinates_cons`). The induction hypothesis bounds the influence after those remaining polarizations by the influence of the once-polarized function. Coordinate polarization itself does not increase influence (`coalitionalInfluenceToward_coordinatePolarization_le`); combining the two inequalities proves the result.

**Key facts.** `FABL.polarizeCoordinates_cons`, `FABL.coalitionalInfluenceToward_coordinatePolarization_le`.
