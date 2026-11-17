<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.pmfLpNorm_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Identity for the Probability Norm

**Claim.** For a finite set Ω, a probability distribution π, p > 0, and f: Ω → ℝ, the p-th power of the absolute value of the probability norm equals the expectation of |f|^p.

**Proof.** The expectation of |f|^p is nonnegative: each integrand is a nonnegative real power of an absolute value, so this follows from expectation nonnegativity (FABL.pmfExpectation_nonneg). The norm itself is nonnegative as well (FABL.pmfLpNorm_nonneg), so its absolute value may be removed. By definition, the norm is the p⁻¹ power of the expectation of |f|^p. The composition rule for real powers turns its p-th power into the power with exponent p⁻¹p; because p > 0, this exponent is 1. The result is the original expectation.

**Key facts.** `FABL.pmfExpectation_nonneg`, `FABL.pmfLpNorm_nonneg`.
