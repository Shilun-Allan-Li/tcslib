<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.measurable_rnDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of the density

**Claim.** For probability measures $\mu$ and $\nu$ on $\Omega$, the real-valued Radon–Nikodym density $x\mapsto (d\mu/d\nu)(x)$ is measurable.

**Proof.** Unfolding the definition, the density is the composition of the extended-valued Radon–Nikodym derivative with the map that takes an extended nonnegative real to its real value. The derivative is measurable, and this value-taking map is measurable, so their composition is measurable.
