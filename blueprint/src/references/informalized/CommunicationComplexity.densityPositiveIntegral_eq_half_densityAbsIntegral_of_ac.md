<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.densityPositiveIntegral_eq_half_densityAbsIntegral_of_ac -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive density part and absolute deviation

**Claim.** For probability measures $\mu$ and $\nu$ with $\mu\ll\nu$, the integral of the density minus one over the region where the density is at least one equals half the integral of its absolute deviation from one.

**Proof.** Let $g$ be the Radon–Nikodym density of $\mu$ with respect to $\nu$, minus one. The density is measurable, so $g$ is measurable (`measurable_rnDensity`); it is integrable (`integrable_rnDensity_sub_one`); and its integral is zero under the absolute-continuity hypothesis (`integral_rnDensity_sub_one_eq_zero_of_ac`). The zero-mean positive-part identity says that for any such integrable function, its integral on the region where it is nonnegative equals half the integral of its absolute value (`integral_nonneg_part_eq_half_integral_abs_of_integral_eq_zero`). Applying that identity to $g$, the nonnegative region is exactly where the density is at least one, yielding the claim.

**Key facts.** `CommunicationComplexity.measurable_rnDensity`, `CommunicationComplexity.integrable_rnDensity_sub_one`, `CommunicationComplexity.integral_rnDensity_sub_one_eq_zero_of_ac`, `CommunicationComplexity.integral_nonneg_part_eq_half_integral_abs_of_integral_eq_zero`.
