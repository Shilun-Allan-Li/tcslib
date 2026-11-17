<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.sum_abs_ambientRestrictionFourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Norm of an Extended Restriction

**Claim.** The sum of the absolute values of the ambient restriction Fourier coefficients equals the Fourier one-norm of the extended restriction.

**Proof.** By the coefficient identity `fourierCoeff_extendedSignRestriction`, the Fourier coefficient of the extended restriction at each coordinate set $S$ equals the corresponding ambient restriction coefficient. Taking absolute values preserves this equality term by term, and summing over all $S$ gives the defining Fourier one-norm.

**Key facts.** `FABL.fourierCoeff_extendedSignRestriction`.
