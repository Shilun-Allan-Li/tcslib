<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.restrictedFourierWeightObservationFromInputs_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on an Input-Derived Observation

**Claim.** For every Boolean target function and every three inputs in the sign cube, the restricted Fourier weight observation formed from those inputs lies in $[-1,1]$.

**Proof.** Split the first input into its fixed-coordinate part and the second and third inputs into their free-coordinate parts using the sign-cube decomposition. The observation formed from these parts lies in $[-1,1]$ by the bound for restricted Fourier weight observations (FABL.restrictedFourierWeightObservation_mem_Icc). Substituting the parts obtained from the three given inputs proves the claim.

**Key facts.** `FABL.restrictedFourierWeightObservation_mem_Icc`.
