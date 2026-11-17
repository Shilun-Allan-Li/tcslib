<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaAuxiliary.lean :: FABL.expect_density_multiplicativeDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Density Average of a Multiplicative Derivative

**Claim.** Averaging the density-weighted multiplicative derivative over directions gives the product of the uniform average of $F$ and the density-weighted average of $F$.

**Proof.** Expand the density expectation and interchange the finite averages over the direction $y$ and the point $z$. For fixed $z$, the factors depending only on $z$ can be taken outside the average over $y$, leaving $\psi(z)F(z)$ multiplied by the average of $F(z+y)$. Translation invariance of the uniform average identifies this inner average with $\mathbb E_x F(x)$ (\texttt{expect\_translate\_add\_viola}). This quantity is independent of $z$, so factor it out of the remaining average. What remains is precisely $\psi$'s weighted average of $F$.

**Key facts.** `FABL.expect_translate_add_viola`.
