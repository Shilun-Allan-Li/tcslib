<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.twoDivPiRademacherSummand_memLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Rademacher summand

**Claim.** For any coefficient function, coordinate, and extended nonnegative exponent $p$, the function $x\mapsto a(i)x_i$ belongs to $L^p$ under the uniform measure on sign vectors.

**Proof.** The summand is measurable because its domain is finite. At every sign vector, the sign at coordinate $i$ is either $-1$ or $1$ (the two possibilities in `FABL.signValue_eq_neg_one_or_one`). Hence the absolute value of the summand is exactly $|a(i)|$, so it is bounded everywhere by that constant. A measurable function bounded almost everywhere by a finite constant belongs to $L^p$ for every extended nonnegative exponent, giving the result.

**Key facts.** `FABL.signValue_eq_neg_one_or_one`.
