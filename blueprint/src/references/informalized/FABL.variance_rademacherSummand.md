<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.variance_rademacherSummand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Rademacher Summand

**Claim.** For a coordinate function $x\mapsto a_i x_i$ on the uniform sign cube, its variance is $a_i^2$.

**Proof.** The summand has mean zero by the vanishing-integral identity for a Rademacher summand (`integral_rademacherSummand_eq_zero`). For a mean-zero random variable, the variance is its second moment. Under the uniform measure, that second moment is the uniform expectation (`integral_uniformPMF_eq_expect`). Since each sign value is either $-1$ or $1$ (`signValue_eq_neg_one_or_one`), the square of $a_i x_i$ is always $a_i^2$. Its expectation is therefore the constant $a_i^2$, proving the result.

**Key facts.** `FABL.integral_rademacherSummand_eq_zero`, `FABL.signValue_eq_neg_one_or_one`.
