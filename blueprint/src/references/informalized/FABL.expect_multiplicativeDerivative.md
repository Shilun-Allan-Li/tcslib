<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaAuxiliary.lean :: FABL.expect_multiplicativeDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Multiplicative Derivative

**Claim.** For a real-valued function on $(\mathbb F_2)^n$, the uniform expectation over $y$ and then $x$ of $F(x+y)F(x)$ equals the square of the uniform expectation of $F$.

**Proof.** Expand the multiplicative derivative and exchange the order of the two finite averages. For fixed $x$, the factor $F(x)$ is constant in $y$, so the inner average becomes $F(x)\mathbb E_y F(x+y)$. Translation preserves the uniform average, so this inner average of $F(x+y)$ equals $\mathbb E_z F(z)$ (\texttt{FABL.expect\_translate\_add\_viola}). This quantity is independent of $x$ and can be factored out of the remaining average. The result is $(\mathbb E_z F(z))(\mathbb E_x F(x))$, which is the square of the common mean.

**Key facts.** `FABL.expect_translate_add_viola`.
