<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.orthogonalComponent_pairwise_orthogonal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairwise orthogonality of components

**Claim.** For distinct coordinate sets $S$ and $T$, the orthogonal components of any two functions at those respective sets have product inner product zero.

**Proof.** By Plancherel, their inner product is the sum, over multi-indices, of the products of their Fourier coefficients ($\texttt{FABL.FiniteFourierBasis.plancherel}$). The coefficient of a component at a multi-index is the original coefficient when that index has the component's support, and zero otherwise ($\texttt{FABL.FiniteFourierBasis.fourierCoeff_orthogonalComponent}$). For each index, its support cannot equal both $S$ and $T$, since $S\ne T$. Thus at least one of the two component coefficients is zero, so every term in the sum vanishes.

**Key facts.** `FABL.FiniteFourierBasis.plancherel`, `FABL.FiniteFourierBasis.fourierCoeff_orthogonalComponent`.
