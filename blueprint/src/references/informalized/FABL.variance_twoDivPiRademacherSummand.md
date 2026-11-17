<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.variance_twoDivPiRademacherSummand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance of a Rademacher Summand

**Claim.** For every coefficient vector and coordinate, the variance under the uniform sign-cube measure of $x\mapsto a_i x_i$ is $a_i^2$.

**Proof.** The summand has mean zero by the corresponding vanishing-integral identity (`integral_twoDivPiRademacherSummand_eq_zero`), so its variance is its second moment. The integral under the uniform measure is the uniform expectation (`integral_uniformPMF_eq_expect`). Each coordinate sign is $-1$ or $1$ (`signValue_eq_neg_one_or_one`), so squaring $a_i x_i$ gives the constant $a_i^2$. The expectation of this constant is $a_i^2$, as required.

**Key facts.** `FABL.integral_twoDivPiRademacherSummand_eq_zero`, `FABL.signValue_eq_neg_one_or_one`.
