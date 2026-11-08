<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/KLDivergence.lean :: CommunicationComplexity.singleton_mass_mul_llr_eq_log_ratio -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton log-likelihood identity

**Claim.** For finite measures μ and ν with μ absolutely continuous with respect to ν, the mass μ({ω}) multiplied by the log-likelihood ratio at ω equals that mass multiplied by the logarithm of the ratio of the singleton masses.

**Proof.** Split into two cases. If μ({ω}) = 0, its real-valued mass is zero, so both products vanish. Otherwise, absolute continuity implies ν({ω}) ≠ 0: if ν({ω}) were zero, μ({ω}) would also be zero. The Radon–Nikodym derivative at ω is therefore the ratio μ({ω})/ν({ω}), by the singleton ratio formula (CommunicationComplexity.rnDeriv_toReal_eq_singleton_ratio). Substituting this into the definition of the log-likelihood ratio gives the claimed equality.

**Key facts.** `CommunicationComplexity.rnDeriv_toReal_eq_singleton_ratio`.
