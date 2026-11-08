<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.spectralPNorm_one_setIndicator_binaryAffineSubspace -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Spectral one-norm of an affine-subspace indicator

**Claim.** For a linear subspace $H$ and a vector $a$, the spectral one-norm of the indicator of the affine subspace $H+a$ is $1$.

**Proof.** The spectral one-norm at exponent one is defined by a sum whose simplification yields the sum of the absolute values of the Fourier coefficients. The upstream result \(\texttt{sum\_abs\_vectorFourierCoeff\_setIndicator\_binaryAffineSubspace}\) states directly that this sum equals $1$ for the indicator of $H+a$. Substitution gives the asserted value.

**Key facts.** `FABL.sum_abs_vectorFourierCoeff_setIndicator_binaryAffineSubspace`.
