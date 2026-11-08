<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.uniformLpNorm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Uniform Norm

**Claim.** Let $\Omega$ be a finite set, let $q>0$, and let $f\colon\Omega\to\mathbb R$. The uniform $L^{q/2}$ norm of $x\mapsto f(x)^2$ equals the square of the uniform $L^q$ norm of $f$.

**Proof.** Apply the power rule for the uniform norm with exponent $c=2$ (\texttt{uniformLpNorm_abs_rpow}): the uniform $L^{q/2}$ norm of $x\mapsto |f(x)|^2$ is the square of the uniform $L^q$ norm of $f$. Since $|f(x)|^2=f(x)^2$, this is the claimed identity.

**Key facts.** `FABL.uniformLpNorm_abs_rpow`.
