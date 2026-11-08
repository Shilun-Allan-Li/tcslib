<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/BooleanInfluence.lean :: FABL.setCoordinate_eq_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating by the Existing Value

**Claim.** For any sign vector and coordinate, replacing that coordinate by its current value leaves the vector unchanged.

**Proof.** A function update changes a function only at the specified coordinate, where it assigns the new value. Here the assigned value is already the value of the vector at that coordinate, so every coordinate retains its original value. Hence the updated vector equals the original vector.
