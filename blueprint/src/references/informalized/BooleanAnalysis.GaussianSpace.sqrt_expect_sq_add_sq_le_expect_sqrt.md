<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Cube.lean :: BooleanAnalysis.GaussianSpace.sqrt_expect_sq_add_sq_le_expect_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity of the Euclidean Norm Under Expectation

**Claim.** For real-valued functions $u,v$ on the Boolean cube, the Euclidean norm of their expectations is at most the expectation of their pointwise Euclidean norm: $\sqrt{(\E[u])^2+(\E[v])^2}\le\E[\sqrt{u^2+v^2}]$.

**Proof.** Express each Boolean-cube expectation as the finite uniform expectation. Regard $(u(x),v(x))$ as the complex number $u(x)+iv(x)$. Linearity of expectation in the real and imaginary coordinates identifies the expectation of this complex-valued function with $(\E[u])+i(\E[v])$. The norm of an expectation is at most the expectation of the norm, by the triangle inequality for finite averages. The complex norm of $a+ib$ is $\sqrt{a^2+b^2}$, so this inequality is exactly the claimed bound.

**Key facts.** `BooleanAnalysis.expect_eq_fintypeExpect`.
