<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.pmfLpNorm_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the Probability Norm

**Claim.** For a finite set Ω, a probability distribution π, a real number p, and f: Ω → ℝ, the probability norm of order p is nonnegative.

**Proof.** For every x, the real power |f(x)|^p is nonnegative, since a real power of a nonnegative base is nonnegative. The expectation of this pointwise nonnegative function is nonnegative by the nonnegativity of expectation (FABL.pmfExpectation_nonneg). The norm is a real power of that expectation, and a real power of a nonnegative base is again nonnegative. Hence the norm is nonnegative.

**Key facts.** `FABL.pmfExpectation_nonneg`.
