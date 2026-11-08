<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.uniformLpNorm_two_eq_sqrt_expect_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Norm as Root Mean Square

**Claim.** For a finite set $\Omega$ and $f\colon\Omega\to\mathbb R$, the uniform $2$-norm of $f$ equals the square root of the uniform expectation of $f(x)^2$.

**Proof.** The uniform $2$-norm is nonnegative: its defining expectation is nonnegative, and taking a real power with exponent $1/2$ preserves nonnegativity. Thus it equals its absolute value, which in turn equals the square root of its square. The squared uniform $2$-norm is the uniform expectation of $f(x)^2$ (\texttt{uniformLpNorm_two_sq_eq_expect_sq}); substituting this identity gives the result.

**Key facts.** `FABL.uniformLpNorm_two_sq_eq_expect_sq`.
