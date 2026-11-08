<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.integral_rnDensity_eq_one_of_ac -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral of the density

**Claim.** If $\mu$ and $\nu$ are probability measures and $\mu\ll\nu$, then the real-valued Radon–Nikodym density integrates to one against $\nu$.

**Proof.** The Radon–Nikodym theorem's integral identity for the real-valued derivative states that, under $\mu\ll\nu$, its integral with respect to $\nu$ equals the total mass of $\mu$. Since $\mu$ is a probability measure, that total mass is one. Expressing the derivative in the real-valued density notation yields the asserted formula.
