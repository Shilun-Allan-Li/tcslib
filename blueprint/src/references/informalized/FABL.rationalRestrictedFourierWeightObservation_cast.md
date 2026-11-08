<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.rationalRestrictedFourierWeightObservation_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Casting the Restricted Weight Observation

**Claim.** The rational observation formed from the two labels and their lifted Fourier observations, viewed as a real number, equals the product of the corresponding real restricted Fourier coefficient observations.

**Proof.** Apply the rational-to-real Fourier observation identity (`rationalFourierObservation_cast`) separately to the two samples obtained by combining each free assignment with the fixed assignment. The rational weight is their product, so after these replacements it is the product of the two real Fourier observations. Unfolding the restricted observation definitions identifies each factor with the corresponding restricted coefficient observation, giving the claimed equality.

**Key facts.** `FABL.rationalFourierObservation_cast`.
