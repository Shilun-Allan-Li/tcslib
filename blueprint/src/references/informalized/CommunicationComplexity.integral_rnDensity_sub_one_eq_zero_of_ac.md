<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.integral_rnDensity_sub_one_eq_zero_of_ac -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero mean of the centered density

**Claim.** If $\mu$ and $\nu$ are probability measures with $\mu\ll\nu$, then the Radon–Nikodym density minus one has integral zero against $\nu$.

**Proof.** By integrability of the density, linearity of the integral gives $\int (d\mu/d\nu-1)\,d\nu=\int (d\mu/d\nu)\,d\nu-\int 1\,d\nu$. The first integral is one by the identity that the density integrates to the total mass of $\mu$ (`CommunicationComplexity.integral_rnDensity_eq_one_of_ac`). The second is one because $\nu$ is a probability measure. Their difference is zero.

**Key facts.** `CommunicationComplexity.integrable_rnDensity`, `CommunicationComplexity.integral_rnDensity_eq_one_of_ac`.
