<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.exists_nonzero_dualFourierCoeff_subspaceRestriction_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Fourier Coefficient on a Kernel

**Claim.** If a nonzero Fourier coefficient is present and the Fourier support is smaller than the dual space, some nonzero linear functional has a kernel on which a Fourier coefficient of the restriction equals the given coefficient.

**Proof.** Because the Fourier support has cardinality strictly smaller than the full dual space, choose a functional $\eta$ outside that support. Its Fourier coefficient is therefore zero. The given frequency $\gamma$ belongs to the support, so $\gamma\ne\eta$. Set $\beta=\gamma+\eta$. Over the field with two elements, $\beta$ is nonzero: otherwise $\gamma=\eta$. Let $H=\ker\beta$ and let $\phi$ be the restriction of $\gamma$ to $H$. The restriction-sum identity for Fourier coefficients (`dualFourierCoeff_subspaceRestriction_eq_sum_fiber`) expresses the coefficient of $f|_H$ at $\phi$ as the sum over ambient frequencies restricting to $\phi$. The kernel fiber description (`dualRestrict_ker_fiber_iff`) says precisely that these frequencies are $\gamma$ and $\gamma+\beta=\eta$. Thus the sum is the coefficient at $\gamma$ plus the coefficient at $\eta$. The latter is zero by choice of $\eta$, leaving exactly the original coefficient.

**Key facts.** `FABL.dualFourierCoeff_subspaceRestriction_eq_sum_fiber`, `FABL.dualRestrict_ker_fiber_iff`.
