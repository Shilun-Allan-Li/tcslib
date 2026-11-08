<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.hammingBallRademacherSummand_memLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalized Coordinate Integrability

**Claim.** Every normalized Rademacher coordinate function on the sign cube belongs to $L^p$ for every exponent $p\in[0,\infty]$.

**Proof.** The coordinate function is measurable because its domain is finite. Its absolute value is bounded by the normalization coefficient: each sign has value either $-1$ or $1$ (`signValue_eq_neg_one_or_one`), and the coefficient is nonnegative (`normalizedRademacherCoefficient_nonneg`). A measurable function bounded in norm belongs to $L^p$ for every exponent, including the endpoints, so the summand has the claimed integrability.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`, `FABL.normalizedRademacherCoefficient_nonneg`.
