<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SpectralDegree.lean :: FABL.two_pow_functionAlgebraicDegree_le_spectralSparsity_booleanRealEmbedding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree and spectral sparsity

**Claim.** For a nonzero Boolean function $f:\{0,1\}^n\to\mathbb F_2$, its spectral sparsity after Boolean real embedding is at least $2^{\deg_2(f)}$.

**Proof.** Choose a set $S$ supporting a nonzero algebraic-normal-form coefficient of maximal size; the maximality lemma gives $|S|=\deg_2(f)$ (\texttt{FABL.exists\_top\_anfCoeff}). Fix any subset $A\subseteq S$. The odd-restriction-coefficient lemma supplies an odd integer $z$ such that the corresponding restricted Fourier coefficient at the zero fixed-sign input is $z\,2^{-|S|}$ (\texttt{FABL.exists\_odd\_restrictionFourierCoeff}). An odd integer is nonzero, so this restricted coefficient is nonzero.

The restricted coefficient is a sum over extensions of $A$ to frequencies on all coordinates: each term is the full Fourier coefficient of the Boolean real embedding at that extension, multiplied by the corresponding indexed monomial (\texttt{FABL.restrictionFourierCoeff\_eq\_sum}). Since the sum is nonzero, at least one extension has a nonzero full Fourier coefficient. Choose one such extension for each $A$. It belongs to the vector Fourier support, because vector Fourier coefficients agree with the full Fourier coefficients at the support set of the associated Boolean cube point (\texttt{FABL.vectorFourierCoeff\_eq\_fourierCoeff\_binaryFunctionOnSignCube}; support membership is characterized by a nonzero coefficient in \texttt{FABL.mem\_vectorFourierSupport}).

These chosen extensions are distinct for distinct $A$: on coordinates in $S$, an extension records exactly which coordinates belong to $A$, while its fixed-coordinate part lies outside that free-coordinate encoding. Thus the construction injects the subsets of $S$ into the vector Fourier support. There are $2^{|S|}$ such subsets, so the support has at least that many elements. Finally, vector Fourier support has cardinality equal to spectral sparsity (\texttt{FABL.spectralSparsity\_eq\_card\_vectorFourierSupport}); substituting $|S|=\deg_2(f)$ proves the bound.

**Key facts.** `FABL.exists_top_anfCoeff`, `FABL.exists_odd_restrictionFourierCoeff`, `FABL.restrictionFourierCoeff_eq_sum`, `FABL.vectorFourierCoeff_eq_fourierCoeff_binaryFunctionOnSignCube`, `FABL.mem_vectorFourierSupport`, `FABL.spectralSparsity_eq_card_vectorFourierSupport`.
