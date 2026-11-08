<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.dualSpectralSparsity_subspaceRestriction_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Spectral sparsity under subspace restriction

**Claim.** The number of nonzero Fourier coefficients of the restriction of $f$ to $H$ is at most the number of nonzero Fourier coefficients of $f$.

**Proof.** Take any functional $\phi$ on $H$ whose restricted-function coefficient is nonzero. The fiber-sum formula expresses that coefficient as a sum over functionals $\psi$ on $V$ restricting to $\phi$ (\texttt{FABL.dualFourierCoeff_subspaceRestriction_eq_sum_fiber}). If none of those $\psi$ had a nonzero coefficient of $f$, every term in the sum would vanish, contradicting the choice of $\phi$. Thus each supported functional on $H$ lies in the image of the support of $f$ under restriction. The support membership criterion is \texttt{FABL.mem_dualFourierSupport}. Consequently, the restricted support has cardinality at most the cardinality of that image, which is at most the cardinality of the original support.

**Key facts.** `FABL.mem_dualFourierSupport`, `FABL.dualFourierCoeff_subspaceRestriction_eq_sum_fiber`.
