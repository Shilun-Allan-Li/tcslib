<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.integrable_rnDensity_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of the centered density

**Claim.** For probability measures $\mu$ and $\nu$, the Radon–Nikodym density minus one is integrable with respect to $\nu$.

**Proof.** The Radon–Nikodym density is integrable with respect to $\nu$ (by `CommunicationComplexity.integrable_rnDensity`). The constant function with value $1$ is also integrable, since $\nu$ is a probability measure and hence finite. Integrability is preserved under subtraction, so their difference is integrable.

**Key facts.** `CommunicationComplexity.integrable_rnDensity`.
