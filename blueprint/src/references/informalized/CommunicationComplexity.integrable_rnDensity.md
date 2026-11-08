<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.integrable_rnDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of the Radon–Nikodym density

**Claim.** The real-valued Radon–Nikodym density of one probability measure with respect to another is integrable with respect to the latter measure.

**Proof.** The real-valued Radon–Nikodym derivative is integrable by the standard integrability theorem for the real conversion of a Radon–Nikodym derivative (`Measure.integrable_toReal_rnDeriv`). Applying that theorem to the two probability measures gives the assertion.
