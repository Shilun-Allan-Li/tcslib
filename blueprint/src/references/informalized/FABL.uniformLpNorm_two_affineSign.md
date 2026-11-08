<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.uniformLpNorm_two_affineSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Norm of an Affine Sign Function

**Claim.** For real numbers $a,b$, the uniform $2$-norm of $s\mapsto a+bs$ on $\{-1,1\}$ is $\sqrt{a^2+b^2}$.

**Proof.** The uniform $2$-norm is the square root of the uniform expectation of the square (\texttt{uniformLpNorm_two_eq_sqrt_expect_sq}). The two inputs give values $a+b$ and $a-b$, so that expectation is $\big((a+b)^2+(a-b)^2\big)/2=a^2+b^2$. Taking the nonnegative square root yields the result.

**Key facts.** `FABL.uniformLpNorm_two_eq_sqrt_expect_sq`.
