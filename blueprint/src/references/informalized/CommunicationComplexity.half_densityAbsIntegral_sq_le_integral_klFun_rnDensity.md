<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.half_densityAbsIntegral_sq_le_integral_klFun_rnDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relative entropy controls squared density deviation

**Claim.** For probability measures $\mu$ and $\nu$ with $\mu\ll\nu$, if the log-likelihood ratio is integrable under $\mu$, then one half the square of the $\nu$-integral of the absolute deviation of the Radon–Nikodym density from $1$ is at most the $\nu$-integral of the scalar KL function evaluated at that density.

**Proof.** First, the assumed integrability of the log-likelihood ratio, together with absolute continuity, implies that the scalar KL function of the Radon–Nikodym density is integrable under $\nu$; this is the integrability characterization for the KL function of a Radon–Nikodym derivative. Now apply the bound for a nonnegative integrable function of mean one: if $f\ge 0$, $\int f\,d\nu=1$, and the KL function of $f$ is integrable, then $\frac12(\int |f-1|\,d\nu)^2\le\int \mathrm{klFun}(f)\,d\nu$. Take $f$ to be the Radon–Nikodym density of $\mu$ with respect to $\nu$. It is measurable (`CommunicationComplexity.measurable_rnDensity`), integrable (`CommunicationComplexity.integrable_rnDensity`), nonnegative (`CommunicationComplexity.rnDensity_nonneg`), and has integral one under the absolute-continuity hypothesis (`CommunicationComplexity.integral_rnDensity_eq_one_of_ac`). The general bound then gives the claimed inequality.

**Key facts.** `CommunicationComplexity.measurable_rnDensity`, `CommunicationComplexity.integrable_rnDensity`, `CommunicationComplexity.half_integral_abs_sub_one_sq_le_integral_klFun`, `CommunicationComplexity.rnDensity_nonneg`, `CommunicationComplexity.integral_rnDensity_eq_one_of_ac`.

**Caveat.** The supplied informal statement describes a different Pinsker-type bound. This account follows the formal statement and proof source, which establish an inequality for the Radon–Nikodym density and the scalar KL function.
