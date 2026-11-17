<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/Estimator.lean :: FABL.restrictedFourierWeightEstimatorOutput_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Form of the Estimator Output

**Claim.** Viewed as a real number, the rational restricted Fourier weight estimator output equals the sum of the corresponding real restricted Fourier weight observations divided by $m$.

**Proof.** Express the rational estimator output as the sum of its $m$ rational input-derived observations divided by $m$ (FABL.restrictedFourierWeightEstimatorOutput_eq_sum). For each input triple, the rational observation, when viewed in $\mathbb R$, equals the corresponding real observation (FABL.rationalRestrictedFourierWeightObservationFromInputs_cast). Casting the finite sum and quotient to the reals therefore gives the sum of those real observations divided by $m$, which is the real estimator output by definition.

**Key facts.** `FABL.rationalRestrictedFourierWeightObservationFromInputs_cast`, `FABL.restrictedFourierWeightEstimatorOutput_eq_sum`.
