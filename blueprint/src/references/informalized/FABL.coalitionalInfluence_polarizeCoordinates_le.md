<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluence_polarizeCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polarization Reduces Coalitional Influence

**Claim.** Successively polarizing a Boolean function in any finite list of coordinates does not increase its coalitional influence on a fixed coordinate set $J$.

**Proof.** Induct on the list of coordinates, keeping the initial function general. For the empty list, polarization leaves the function unchanged, so the two influences are equal. For a list beginning with $i$ and followed by a shorter list, the recursive definition says to first polarize the function at $i$, then apply the remaining polarizations. The induction hypothesis bounds the influence after those remaining steps by that of the once-polarized function. The one-coordinate polarization inequality (`FABL.coalitionalInfluence_coordinatePolarization_le`) bounds this in turn by the influence of the original function. Combining the inequalities proves the result.

**Key facts.** `FABL.polarizeCoordinates_cons`, `FABL.coalitionalInfluence_coordinatePolarization_le`.
