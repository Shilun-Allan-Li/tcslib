<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.density_l1_pinsker_le_kl_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Density deviation bounded by relative entropy

**Claim.** For probability measures $\mu$ and $\nu$ with $\mu\ll\nu$, if the log-likelihood ratio is integrable under $\mu$, then half the square of the density's $L^1(\nu)$ deviation from one is at most the integral of the log-likelihood ratio under $\mu$.

**Proof.** First apply the established bound on the density deviation by the integral of the KL function of the density (`half_densityAbsIntegral_sq_le_integral_klFun_rnDensity`), using absolute continuity and the assumed integrability. Then identify that KL-function integral under $\nu$ with the log-likelihood-ratio integral under $\mu$ (`integral_klFun_rnDeriv_eq_kl_integral`). Combining these gives the inequality in the statement.

**Key facts.** `CommunicationComplexity.half_densityAbsIntegral_sq_le_integral_klFun_rnDensity`, `CommunicationComplexity.integral_klFun_rnDeriv_eq_kl_integral`.

**Caveat.** The supplied informal statement describes a different Pinsker inequality involving statistical distance and a binary event. The formal statement and proof source instead establish the density-integral inequality stated in this claim.
