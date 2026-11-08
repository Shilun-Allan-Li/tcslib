<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.pinsker_inequality_of_ac -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pinsker inequality under absolute continuity

**Claim.** If $\mu\ll\nu$ are probability measures, then $\operatorname{ofReal}(2\,\mathrm{tvDistance}(\mu,\nu)^2)\le \mathrm{klDiv}(\mu,\nu)$.

**Proof.** Split according to whether the log-likelihood ratio is integrable with respect to $\mu$. If it is, the Pinsker inequality under absolute continuity and integrability applies. If it is not, the KL divergence is infinite by the nonintegrability characterization, so the claimed extended-real inequality follows from the fact that every extended nonnegative real is at most infinity.

**Key facts.** `CommunicationComplexity.pinsker_inequality_of_ac_of_integrable`.
