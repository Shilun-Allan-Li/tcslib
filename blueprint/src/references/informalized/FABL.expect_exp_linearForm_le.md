<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/SharpLevelOneInequality.lean :: FABL.expect_exp_linearForm_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Moment Bound

**Claim.** For a uniformly chosen sign vector $x$, the exponential moment of the linear form with coefficients $a_i$ is at most $\exp\!\left(\frac12\sum_i a_i^2\right)$.

**Proof.** Write the exponential of the sum defining the linear form as the product of the coordinate exponentials. Since the uniform measure on the sign cube is the product of the uniform measures on its coordinates, the average of this product factors as the product of the one-coordinate averages. Each coordinate average is $\cosh(a_i)$: the two signs occur equally often, and averaging $e^{a_i}$ and $e^{-a_i}$ gives this hyperbolic cosine (using the sign-average formula, `expect_sign`). The inequality $\cosh(t)\leq e^{t^2/2}$ then bounds each factor. Multiplying these bounds and combining exponentials gives $\prod_i e^{a_i^2/2}=e^{(\sum_i a_i^2)/2}$, as required.

**Key facts.** `FABL.expect_sign`.
