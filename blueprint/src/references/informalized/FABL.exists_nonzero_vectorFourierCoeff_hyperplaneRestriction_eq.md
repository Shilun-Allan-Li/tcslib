<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.exists_nonzero_vectorFourierCoeff_hyperplaneRestriction_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Fourier Coefficient on a Hyperplane

**Claim.** If the vector Fourier support has size less than $2^n$, a nonzero vector defines a hyperplane on which the restriction has a Fourier coefficient equal to the given nonzero coefficient.

**Proof.** Apply the kernel-restriction result (`exists_nonzero_vectorFourierCoeff_subspaceRestriction_eq`) to obtain a nonzero linear functional $\psi$ and a frequency on its kernel whose restricted coefficient equals the original vector Fourier coefficient. The vector-to-dual equivalence identifies each vector $\beta$ with the linear functional given by dot product against $\beta$. Take $\beta$ corresponding to $\psi$. This vector is nonzero, since the equivalence sends zero only to the zero functional. Its dot-product hyperplane is exactly $\ker\psi$, so the coefficient equality supplied by the kernel result is the required one.

**Key facts.** `FABL.exists_nonzero_vectorFourierCoeff_subspaceRestriction_eq`.
