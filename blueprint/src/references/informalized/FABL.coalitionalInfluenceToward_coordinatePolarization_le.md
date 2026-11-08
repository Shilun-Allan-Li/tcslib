<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coalitionalInfluenceToward_coordinatePolarization_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polarization and Coalitional Influence

**Claim.** The coalitional influence toward either sign does not increase when the function is polarized in a coordinate.

**Proof.** Expand coalitional influence as the coalition success probability minus the probability that the function already equals the target sign. Coordinate polarization preserves the latter probability (by `uniformProbability_coordinatePolarization_eq`), while it can only decrease the coalition success probability (by `coalitionSuccessProbability_coordinatePolarization_le`). Subtracting the same quantity from both sides of the success-probability inequality gives the claimed bound.

**Key facts.** `FABL.uniformProbability_coordinatePolarization_eq`, `FABL.coalitionSuccessProbability_coordinatePolarization_le`.
