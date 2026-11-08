<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.exists_nonzero_vectorFourierCoeff_subspaceRestriction_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Fourier Coefficient on a Subspace Kernel

**Claim.** If the vector Fourier support has size less than $2^n$ and contains $\gamma$, there is a nonzero functional $\beta$ and a frequency on its kernel for which the restricted Fourier coefficient equals the coefficient at $\gamma$.

**Proof.** Translate the given vector frequency $\gamma$ into a linear functional using the vector-dual equivalence. The Fourier coefficient correspondence (`dualFourierCoeff_vectorDualEquiv`) shows that this functional has the same nonzero coefficient, hence lies in the dual Fourier support. The support-size correspondence (`dualSpectralSparsity_eq_spectralSparsity`) and the fact that the dual space has $2^n$ elements transfer the strict sparsity bound to that dual space. Apply the dual kernel-restriction theorem (`exists_nonzero_dualFourierCoeff_subspaceRestriction_eq`) to get a nonzero functional $\beta$ and a frequency on its kernel preserving the coefficient. The coefficient correspondence again identifies the original coefficient at the vector frequency with the one at its associated functional, giving the desired equality.

**Key facts.** `FABL.dualFourierCoeff_vectorDualEquiv`, `FABL.dualSpectralSparsity_eq_spectralSparsity`, `FABL.exists_nonzero_dualFourierCoeff_subspaceRestriction_eq`, `FABL.mem_dualFourierSupport`, `FABL.mem_vectorFourierSupport`.
