<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.mean_coordinatePolarization -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Preserved by Coordinate Polarization

**Claim.** Replacing the values of a Boolean function at a chosen coordinate by their maximum when that coordinate is $+1$ and their minimum when it is $-1$ preserves the mean.

**Proof.** First apply coordinate averaging to the polarized function. Its coordinate average agrees pointwise with the coordinate average of the original function: the two values being averaged are the same pair, merely assigned in maximum/minimum order (FABL.coordinateExpectation_coordinatePolarization_toReal). The mean is unchanged by coordinate averaging (FABL.mean_coordinateExpectation). Therefore the mean of the polarized function equals the mean of its coordinate average, which equals the mean of the original function's coordinate average, and hence equals the original mean.

**Key facts.** `FABL.mean_coordinateExpectation`, `FABL.coordinateExpectation_coordinatePolarization_toReal`.
