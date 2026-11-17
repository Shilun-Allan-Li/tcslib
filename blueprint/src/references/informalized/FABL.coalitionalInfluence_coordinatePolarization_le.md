<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluence_coordinatePolarization_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polarization Decreases Coalitional Influence

**Claim.** The coalitional influence of the coordinate-polarized function on $J$ is at most that of the original function on $J$.

**Proof.** Express the total coalitional influence as the sum of the influences toward $+1$ and $-1$ (`coalitionalInfluence_eq_toward_add_toward`). Coordinate polarization does not increase the influence toward either target sign (`coalitionalInfluenceToward_coordinatePolarization_le`). Adding these two inequalities gives the desired bound.

**Key facts.** `FABL.coalitionalInfluence_eq_toward_add_toward`, `FABL.coalitionalInfluenceToward_coordinatePolarization_le`.
