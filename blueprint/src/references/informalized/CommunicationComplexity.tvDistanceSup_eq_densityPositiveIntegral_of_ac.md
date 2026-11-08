<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.tvDistanceSup_eq_densityPositiveIntegral_of_ac -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total variation as positive excess mass

**Claim.** For probability measures μ and ν with μ absolutely continuous with respect to ν, the supremum over measurable sets of |μ(S) − ν(S)| equals the integral of the density excess over the region where the density is at least one.

**Proof.** Set g(x) = rnDensity μ ν x − 1. For every measurable set S, the measure difference μ(S) − ν(S) equals the integral of g over S (CommunicationComplexity.measureReal_sub_eq_setIntegral_rnDensity_sub_one). Consequently, the range of absolute measure differences over measurable sets agrees with the range of absolute set integrals of g, and so the two suprema agree. The density is measurable (CommunicationComplexity.measurable_rnDensity), hence g is measurable; it is integrable (CommunicationComplexity.integrable_rnDensity_sub_one) and has integral zero (CommunicationComplexity.integral_rnDensity_sub_one_eq_zero_of_ac). The supremum formula for a measurable, integrable, mean-zero function (CommunicationComplexity.sSup_abs_setIntegral_eq_nonneg_part_of_integral_eq_zero) therefore identifies this supremum with the integral of g over {x : g(x) ≥ 0}. This set is exactly the region where the density is at least one, and there g is the density excess, giving the result.

**Key facts.** `CommunicationComplexity.measureReal_sub_eq_setIntegral_rnDensity_sub_one`, `CommunicationComplexity.measurable_rnDensity`, `CommunicationComplexity.integrable_rnDensity_sub_one`, `CommunicationComplexity.integral_rnDensity_sub_one_eq_zero_of_ac`, `CommunicationComplexity.sSup_abs_setIntegral_eq_nonneg_part_of_integral_eq_zero`.
