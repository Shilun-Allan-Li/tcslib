<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Taylor.lean :: BooleanAnalysis.GaussianSpace.affine_replacement_bound_c3 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Third-Order Affine Replacement Bound

**Claim.** If $X$ and $Y$ have finite third moments, equal means, and equal second moments, then for a three times continuously differentiable function with third derivative bounded in absolute value by $C$, the difference of the expectations of $\psi(a+bX)$ and $\psi(a+bY)$ is at most $\frac C6|b|^3$ times the sum of their third absolute moments.

**Proof.** 1. The expectations of the two degree-two Taylor polynomials agree. Indeed, integrating each polynomial expresses it using the zeroth, first, and second moments; the zeroth moments agree because both measures are probabilities, and the first and second moments agree by hypothesis. This is the role of the integrated Taylor polynomial identity (`integral_taylor_polynomial`).

2. Apply the integral Taylor remainder estimate (`abs_integral_sub_taylor_polynomial_le`) with order two separately to $X$ and $Y$. Each expectation differs from its integrated degree-two Taylor polynomial by at most $\frac C6|b|^3$ times the corresponding third absolute moment.

3. Insert the common polynomial expectation between the two expectations and apply the triangle inequality. The two remainder bounds add to the claimed expression.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_taylor_polynomial`, `BooleanAnalysis.GaussianSpace.abs_integral_sub_taylor_polynomial_le`.
