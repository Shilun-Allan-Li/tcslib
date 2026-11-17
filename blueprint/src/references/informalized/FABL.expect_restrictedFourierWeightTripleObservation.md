<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.expect_restrictedFourierWeightTripleObservation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triple-Input Restricted Fourier Identity

**Claim.** Averaging the triple-input observation over three independent uniform full sign vectors gives the restricted Fourier weight of the real-valued sign function associated to the target.

**Proof.** Factor the uniform expectation over the three input coordinates into an iterated expectation: first over the input used to supply the fixed coordinates, then over each of the two inputs supplying free coordinates. This uses the product rule for finite uniform expectations. The resulting three nested averages are exactly the expected observation from inputs. The identity that this iterated expectation equals the restricted Fourier weight is the observation-to-weight formula (FABL.expect_restrictedFourierWeightObservationFromInputs_eq_restrictedFourierWeight).

**Key facts.** `FABL.expect_restrictedFourierWeightObservationFromInputs_eq_restrictedFourierWeight`.
