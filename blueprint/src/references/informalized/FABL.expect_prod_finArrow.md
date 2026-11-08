<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.expect_prod_finArrow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a product over a finite power

**Claim.** For functions $f_i$ on a finite type $\alpha$, the uniform expectation over tuples $(y_i)_{i<s}$ of $\prod_{i<s}f_i(y_i)$ is the product of the individual uniform expectations.

**Proof.** Proceed by induction on $s$. For $s=0$, both sides are empty products and equal $1$. For the induction step, identify a tuple of length $s+1$ with its first coordinate together with its tail of length $s$. Under this bijection, the product separates into the factor for coordinate $0$ and the product over the tail. The uniform expectation over the resulting product space factors into iterated expectations. Since the first factor depends only on the first coordinate and the tail product only on the tail, the expectation of their product is the product of their expectations. Apply the induction hypothesis to the tail functions, then combine the first-coordinate factor with the tail product to obtain the product of all $s+1$ individual expectations.
