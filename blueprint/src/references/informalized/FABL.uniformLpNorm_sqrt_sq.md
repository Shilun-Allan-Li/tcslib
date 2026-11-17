<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.uniformLpNorm_sqrt_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Norm of a Square Root

**Claim.** Let $\Omega$ be finite, $q>0$, and let $H\colon\Omega\to\mathbb R$ be nonnegative. The square of the uniform $q$-norm of $x\mapsto\sqrt{H(x)}$ equals the uniform $(q/2)$-norm of $H$.

**Proof.** The power rule for the uniform norm (\texttt{uniformLpNorm_abs_rpow}), used with exponent $2$, identifies the uniform $(q/2)$-norm of $x\mapsto |\sqrt{H(x)}|^2$ with the square of the uniform $q$-norm of $x\mapsto\sqrt{H(x)}$. Because the square root is nonnegative and $H(x)\ge 0$, its absolute value is itself and $(\sqrt{H(x)})^2=H(x)$. Thus the function inside the first norm is exactly $H$.

**Key facts.** `FABL.uniformLpNorm_abs_rpow`.
