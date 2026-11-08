<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.pinsker_inequality_of_ac_of_integrable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extended-real Pinsker inequality

**Claim.** For probability measures $\mu$ and $\nu$ with $\mu\ll\nu$ and integrable log-likelihood ratio, $\operatorname{ofReal}(2\,\mathrm{tvDistance}(\mu,\nu)^2)\le \mathrm{klDiv}(\mu,\nu)$.

**Proof.** Under absolute continuity and integrability, the KL divergence equals the real integral of the log-likelihood ratio. The real Pinsker inequality bounds $2\,\mathrm{tvDistance}(\mu,\nu)^2$ above by that integral. Applying the monotonicity of the map taking a nonnegative real to its extended-real value gives the stated inequality.

**Key facts.** `CommunicationComplexity.real_pinsker_inequality_of_ac_of_integrable`.
