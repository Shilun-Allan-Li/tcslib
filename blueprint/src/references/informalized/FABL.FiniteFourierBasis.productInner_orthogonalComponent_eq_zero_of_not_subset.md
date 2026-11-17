<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.productInner_orthogonalComponent_eq_zero_of_not_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orthogonality outside the coordinate support

**Claim.** If $g$ depends only on coordinates in $T$ and the set $S$ is not contained in $T$, then the inner product of $g$ with the orthogonal component of $f$ at support $S$ is zero.

**Proof.** Expand the inner product by Plancherel as a sum of products of Fourier coefficients. The coefficient of the orthogonal component at a multi-index $a$ is the coefficient of $f$ when the support of $a$ is exactly $S$, and is zero otherwise. In the latter case the summand vanishes immediately. In the former case, $S\not\subseteq T$ means that the support of $a$ is not contained in $T$. A function depending only on $T$ has zero Fourier coefficient at every index whose support is not contained in $T$. Hence this summand also vanishes, and every term in the sum is zero.

**Key facts.** `FABL.FiniteFourierBasis.plancherel`, `FABL.FiniteFourierBasis.fourierCoeff_orthogonalComponent`, `FABL.FiniteFourierBasis.fourierCoeff_eq_zero_of_dependsOnly`.
