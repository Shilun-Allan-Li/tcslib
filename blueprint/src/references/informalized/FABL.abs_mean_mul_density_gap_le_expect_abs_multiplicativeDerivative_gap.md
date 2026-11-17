<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaAuxiliary.lean :: FABL.abs_mean_mul_density_gap_le_expect_abs_multiplicativeDerivative_gap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Density Gap Bound by Derivative Gaps

**Claim.** The product of the absolute uniform mean of $F$ and the absolute difference between its density-weighted and uniform means is bounded by the uniform mean of the absolute derivative gaps.

**Proof.** Average the difference between the density-weighted and uniform expectations of the multiplicative derivative over all directions. The two averaging identities for these derivatives show that this average equals $(\mathbb E F)(\mathbb E_\psi F-\mathbb E F)$: the density-weighted derivative average is $(\mathbb E F)(\mathbb E_\psi F)$, while the uniform derivative average is $(\mathbb E F)^2$ (\(\texttt{FABL.expect_density_multiplicativeDerivative}\), \(\texttt{FABL.expect_multiplicativeDerivative}\)). Taking absolute values identifies the left side of the desired inequality with the absolute value of this average. The absolute value of a finite average is at most the average of the absolute values, which gives the result.

**Key facts.** `FABL.expect_density_multiplicativeDerivative`, `FABL.expect_multiplicativeDerivative`.
