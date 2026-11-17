<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.rademacherSummand_memLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Rademacher summand

**Claim.** For every exponent $p\in[0,\infty]$, the random variable $x\mapsto a_i x_i$ belongs to $L^p$ under the uniform probability measure on sign vectors.

**Proof.** Every sign value is either $-1$ or $1$ (`signValue_eq_neg_one_or_one`). Therefore the absolute value of the summand $a_i x_i$ is exactly $|a_i|$ at every point. The summand is measurable on the finite sign space, and this pointwise bound makes it bounded almost everywhere. A measurable function bounded by a finite constant on a probability space belongs to $L^p$ for every exponent, including the endpoint exponents.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`.
