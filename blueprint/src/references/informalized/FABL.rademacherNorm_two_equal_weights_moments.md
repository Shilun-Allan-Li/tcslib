<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KhintchineKahane.lean :: FABL.rademacherNorm_two_equal_weights_moments -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moments of a two-coordinate norm

**Claim.** For a uniformly random sign vector $x\in\{-1,1\}^2$, the norm of the sum of its coordinates has first moment $1$ and second moment $2$.

**Proof.** The two-coordinate norm identity expresses the norm as $1+\chi(x)$, where $\chi(x)=x_1x_2$ is the monomial on both coordinates. Since this monomial is nonconstant, its uniform expectation is zero (`expect_monomial`); hence the first moment is $1$. For the second moment, the identity $\chi(x)^2=1$ (`monomial_sq`) gives $(1+\chi(x))^2=2+2\chi(x)$. Taking expectations, the constant term contributes $2$ and the monomial term contributes zero, again by `expect_monomial`.

**Key facts.** `FABL.rademacherNorm_two_equal_weights`, `FABL.expect_monomial`, `FABL.monomial_sq`.
