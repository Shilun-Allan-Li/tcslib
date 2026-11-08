<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.real_pinsker_inequality_of_ac_of_integrable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Pinsker inequality

**Claim.** If $\mu\ll\nu$ are probability measures and the log-likelihood ratio is integrable with respect to $\mu$, then $2\,\mathrm{tvDistance}(\mu,\nu)^2\le\int \mathrm{llr}(\mu,\nu)(x)\,d\mu(x)$.

**Proof.** The total variation distance under absolute continuity equals half the integral of the absolute difference between the density and one. Substituting this identity into the left side and simplifying gives $(1/2)$ times the square of the density's absolute-deviation integral. The density-based Pinsker bound for the log-likelihood integral then bounds this quantity above by the stated integral.

**Key facts.** `CommunicationComplexity.tvDistance_eq_half_densityAbsIntegral_of_ac`, `CommunicationComplexity.density_l1_pinsker_le_kl_integral`.
