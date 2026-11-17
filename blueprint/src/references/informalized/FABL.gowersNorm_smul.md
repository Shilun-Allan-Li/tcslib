<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersNorm_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of the Gowers norm

**Claim.** For positive $k$, a real scalar $a$, and a function $f$, the Gowers norm satisfies $\|af\|_{U^k}=|a|\,\|f\|_{U^k}$.

**Proof.** Both sides are nonnegative: the norm is nonnegative (`gowersNorm_nonneg`), and so is the product of $|a|$ with the norm of $f$. It is therefore enough to compare their $2^k$-th powers. The power identity (`gowersNorm_pow`) turns the left power into the diagonal inner product of $af$. Scaling every one of the $2^k$ factors in the cube product shows that this inner product is $a^{2^k}$ times the diagonal inner product of $f$ (`gowersDiagonalInner_smul`). Since $2^k$ is even for positive $k$, this scalar power equals $|a|^{2^k}$ (`pow_two_pow_eq_abs_pow_two_pow`). Using the power identity again identifies the resulting expression with the $2^k$-th power of the right side. Injectivity of positive integer powers on nonnegative reals proves the equality.

**Key facts.** `FABL.gowersNorm_nonneg`, `FABL.gowersNorm_pow`, `FABL.gowersDiagonalInner_smul`, `FABL.pow_two_pow_eq_abs_pow_two_pow`.
