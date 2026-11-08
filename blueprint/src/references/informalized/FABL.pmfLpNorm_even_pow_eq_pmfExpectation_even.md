<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.pmfLpNorm_even_pow_eq_pmfExpectation_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Powers of the Probability Norm

**Claim.** For a finite set Ω, a probability distribution π, a positive integer r, and f: Ω → ℝ, the (2r)-th power of the probability norm of order 2r equals the expectation of f raised to the power 2r.

**Proof.** Set q = 2r, which is positive. The norm power identity (FABL.pmfLpNorm_rpow) identifies the q-th power of the absolute value of the norm with the expectation of |f|^q. Since the norm is nonnegative (FABL.pmfLpNorm_nonneg), its absolute value can be removed. Because q is an even integer, |f(x)|^q = f(x)^q for every x. Substituting this equality into the expectation gives the claim.

**Key facts.** `FABL.pmfLpNorm_rpow`, `FABL.pmfLpNorm_nonneg`.
