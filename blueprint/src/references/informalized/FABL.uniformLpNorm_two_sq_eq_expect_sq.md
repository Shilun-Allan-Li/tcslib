<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BasicFourierFormulas.lean :: FABL.uniformLpNorm_two_sq_eq_expect_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Squared Norm Equals the Second Moment

**Claim.** For a finite set $\Omega$ and $f:\Omega\to\mathbb R$, the square of the uniform $L^2$ norm equals the uniform average of $f(x)^2$.

**Proof.** By definition, the uniform $L^2$ norm is the uniform average of $|f(x)|^2$ raised to the power $1/2$. For real $f(x)$, $|f(x)|^2=f(x)^2$, so the average is the second moment and is nonnegative. The square of its nonnegative square root is the average itself, proving the identity.
