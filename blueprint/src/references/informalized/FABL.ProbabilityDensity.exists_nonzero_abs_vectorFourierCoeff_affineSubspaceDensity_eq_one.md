<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/SmallBias.lean :: FABL.ProbabilityDensity.exists_nonzero_abs_vectorFourierCoeff_affineSubspaceDensity_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Nonzero Fourier Coefficient on an Affine Subspace

**Claim.** For a proper subspace $H$ and a vector $a$, there is a nonzero vector whose vector Fourier coefficient under the uniform density on the affine subspace $H+a$ has absolute value $1$.

**Proof.** First show that the perpendicular subspace $H^\perp$ is nontrivial. If it were zero, the double-perpendicular identity $ (H^\perp)^\perp=H$ (\texttt{perpendicularSubspace_perpendicularSubspace}) would imply that $H$ is the perpendicular subspace of $\{0\}$, which is the whole space: every vector has zero dot product with $0$. This contradicts that $H$ is proper. Therefore $H^\perp$ contains some nonzero vector $\gamma$. For any vector in $H^\perp$, the absolute value of its vector Fourier coefficient under the density on $H+a$ is $1$ (\texttt{abs_vectorFourierCoeff_affineSubspaceDensity_of_mem}). Applying this fact to the chosen nonzero $\gamma$ gives the result.

**Key facts.** `FABL.perpendicularSubspace_perpendicularSubspace`, `FABL.mem_perpendicularSubspace_iff`, `FABL.ProbabilityDensity.abs_vectorFourierCoeff_affineSubspaceDensity_of_mem`.
