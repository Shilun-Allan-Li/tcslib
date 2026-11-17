<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.integrable_abs_rnDensity_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of the absolute density deviation

**Claim.** For probability measures $\mu$ and $\nu$, the absolute deviation of the real Radon–Nikodym density of $\mu$ with respect to $\nu$ from one is integrable with respect to $\nu$.

**Proof.** The signed deviation of the density from one is integrable by `integrable_rnDensity_sub_one`. The absolute value of an integrable real-valued function is integrable, so applying this fact to that deviation proves the claim.

**Key facts.** `CommunicationComplexity.integrable_rnDensity_sub_one`.
