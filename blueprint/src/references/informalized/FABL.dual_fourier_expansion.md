<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/SparseSpectrum.lean :: FABL.dual_fourier_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier expansion on the dual

**Claim.** Every real-valued function on the finite-dimensional vector space has an expansion as a sum of its dual Fourier coefficients times the corresponding dual Walsh characters.

**Proof.** The dual Walsh basis expresses the function as the sum of its basis coefficients multiplied by the basis characters. Evaluating this basis expansion at $x$ gives the stated pointwise expansion. The coefficient of each basis character is its dual Fourier coefficient, by the basis representation formula (`FABL.dualWalshBasis_repr`). Substituting these coefficients yields the claimed identity.

**Key facts.** `FABL.dualWalshBasis_repr`.
