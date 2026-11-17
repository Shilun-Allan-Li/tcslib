<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.expect_one_add_andFunction_mul_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# AND monomial average

**Claim.** For the AND function on the uniform sign cube, the average of $(1+A_w(y))\chi_S(y)$ is $2(1-2^{-w})$ when $S$ is empty, and $2^{1-w}(-1)^{|S|+1}$ otherwise.

**Proof.** Split the integrand into the sum of the monomial and its product with the AND function. The average of the monomial is $1$ for the empty set and $0$ otherwise, by orthogonality of cube monomials (`expect_monomial`). The second average is the Fourier coefficient of the AND function at $S$, by the definition of that coefficient. The coefficient formula (`fourierCoeff_andFunction`) gives $1-2\cdot 2^{-w}$ in the empty case and $-2\cdot 2^{-w}(-1)^{|S|}$ otherwise. Adding the first average yields the stated two expressions.

**Key facts.** `FABL.expect_monomial`, `FABL.fourierCoeff_andFunction`.
