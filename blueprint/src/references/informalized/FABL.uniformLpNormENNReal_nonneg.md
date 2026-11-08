<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLpNormENNReal_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the extended uniform norm

**Claim.** For a finite nonempty set $\Omega$, an extended nonnegative real exponent $q$, and a function $f:\Omega\to\mathbb R$, the extended-exponent uniform norm of $f$ is nonnegative.

**Proof.** By definition, the extended-exponent norm is defined by cases. If $q=\infty$, it is the supremum norm, which is nonnegative by the nonnegativity theorem for the uniform supremum norm (`FABL.uniformLInfinityNorm_nonneg`). If $q\ne\infty$, it is the real-exponent uniform norm at $q.toReal$, which is nonnegative by `FABL.uniformLpNorm_nonneg`. These two cases establish the claim.

**Key facts.** `FABL.uniformLInfinityNorm_nonneg`, `FABL.uniformLpNorm_nonneg`.
