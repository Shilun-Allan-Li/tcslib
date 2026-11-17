<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integral_rademacherSummand_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Rademacher summand

**Claim.** For real coefficients $a=(a_i)_{i=1}^n$ and a coordinate $i$, the expected value of $a_i x_i$ under the uniform sign-vector distribution is zero.

**Proof.** The summand is the constant $a_i$ times the $i$th sign coordinate. The mean of that coordinate is zero (the sign-coordinate mean theorem, `integral_signCoordinate_eq_zero`). Pulling the constant through the integral therefore gives $a_i\cdot 0=0$.

**Key facts.** `FABL.integral_signCoordinate_eq_zero`.
