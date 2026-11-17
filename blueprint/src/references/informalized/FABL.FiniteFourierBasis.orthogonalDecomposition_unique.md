<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.orthogonalDecomposition_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Orthogonal Decomposition

**Claim.** Any decomposition of $f$ whose components depend only on their indexed coordinates and are orthogonal to functions of every strict subset is the canonical orthogonal decomposition of $f$.

**Proof.** Fix a multi-index $a$, and let its support be the coordinates where its index is nonconstant. First show that the Fourier coefficient of the component indexed by $T$ vanishes whenever the support of $a$ differs from $T$. If that support is contained in $T$, the inequality of the two sets makes the containment strict. The product basis function indexed by $a$ depends only on its support, so the decomposition's orthogonality condition makes its inner product with the $T$-component zero; this is precisely the relevant Fourier coefficient. If the support is not contained in $T$, the component depends only on $T$, and the fact that a function depending on $T$ has zero Fourier coefficient at any index whose support is not contained in $T$ gives the same conclusion.

Applying the Fourier coefficient functional to the identity that the components sum to $f$ shows that their Fourier coefficients sum to the coefficient of $f$. For an index $a$ supported exactly on $S$, all terms in that sum except the $S$-term vanish, so the $S$-component has the same coefficient as $f$ at $a$. The canonical $S$-component has exactly that coefficient on indices supported on $S$ and zero on all other indices. The vanishing just proved gives this same coefficient description for the proposed component indexed by $S$. Since Fourier coefficients determine a function uniquely, the two components agree for every $S$, proving equality of the decompositions.

**Key facts.** `FABL.FiniteFourierBasis.productFunction_dependsOnly_support`, `FABL.FiniteFourierBasis.fourierCoeff_eq_zero_of_dependsOnly`, `FABL.FiniteFourierBasis.fourierCoeff_sum`, `FABL.FiniteFourierBasis.fourierCoeff_orthogonalComponent`, `FABL.FiniteFourierBasis.fourierCoeff_injective`.
