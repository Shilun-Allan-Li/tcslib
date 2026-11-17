<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ReasonableProductPolynomials.lean :: FABL.pmfExpectation_centered_affine_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered affine second moment

**Claim.** If $X$ has mean zero, then for real $d,e$, the second moment of $dX+e$ is $d^2\mathbb{E}[X^2]+e^2$.

**Proof.** Expand pointwise: $(Xd+e)^2=X^2d^2+X(2de)+e^2$. Linearity of expectation separates these three terms. Pulling out constants gives $d^2\mathbb{E}[X^2]+2de\mathbb{E}[X]+e^2\mathbb{E}[1]$. The middle term vanishes because $X$ has mean zero, and the expectation of the constant one is one because the distribution is a probability mass function (`FABL.pmfExpectation_const`). Rearranging the remaining terms gives the stated identity.

**Key facts.** `FABL.pmfExpectation_add`, `FABL.pmfExpectation_mul_const`, `FABL.pmfExpectation_const`.
