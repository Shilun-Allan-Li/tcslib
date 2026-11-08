<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.rationalRestrictedFourierWeightObservationFromInputs_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted observation cast

**Claim.** The rational observation formed from the two labels and lifted Fourier observations, regarded as real, equals the product of the corresponding real restricted Fourier coefficient observations.

**Proof.** Split the first input into its fixed-coordinate assignment and the other two inputs into their free-coordinate assignments. Apply the identity for rational restricted weight observations (`rationalRestrictedFourierWeightObservation_cast`) to this fixed assignment and these two free assignments. Its two labels are exactly the target values at the combined free and fixed inputs, and the resulting real product is the restricted Fourier weight observation at those assignments, which is the claimed observation from the three inputs.

**Key facts.** `FABL.rationalRestrictedFourierWeightObservation_cast`.
