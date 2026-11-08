<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersNorm_add_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triangle inequality for the Gowers norm

**Claim.** For positive order $k$, the Gowers norm satisfies $\|f+g\|_{U^k}\leq \|f\|_{U^k}+\|g\|_{U^k}$.

**Proof.** Expand the diagonal inner product of $f+g$ as a sum indexed by choices of which cube vertices contribute $f$ and which contribute $g$ (`gowersDiagonalInner_add_expansion`). For each choice, apply the Gowers Cauchy–Schwarz inequality (`gowers_cauchy_schwarz`) to bound its inner product by the product, over vertices, of the corresponding norms. Summing these products gives exactly $(\|f\|_{U^k}+\|g\|_{U^k})^{2^k}$, by the finite product expansion (`sum_prod_gowersNorm_choice`). Hence the diagonal inner product of $f+g$ is at most this quantity. The norm is nonnegative (`gowersNorm_nonneg`), and its $2^k$-th power equals the diagonal inner product (`gowersNorm_pow`). Since $2^k$ is positive, taking the order-preserving $2^k$-th root yields the triangle inequality.

**Key facts.** `FABL.gowersDiagonalInner_add_expansion`, `FABL.gowers_cauchy_schwarz`, `FABL.sum_prod_gowersNorm_choice`, `FABL.gowersNorm_nonneg`, `FABL.gowersNorm_pow`.
