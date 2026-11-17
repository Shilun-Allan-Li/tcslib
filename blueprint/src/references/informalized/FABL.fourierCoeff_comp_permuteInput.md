<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.fourierCoeff_comp_permuteInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Coefficients Under Coordinate Permutation

**Claim.** For every natural number $n$, every permutation $\pi$ of the $n$ coordinates, every real-valued function $f$ on the sign cube, and every coordinate set $S$, the Fourier coefficient at $S$ of the function obtained by permuting the input coordinates according to $\pi$ equals the Fourier coefficient of $f$ at the image of $S$ under $\pi^{-1}$.

**Proof.** Reindex the expectation by the bijection of the sign cube induced by $\pi$. After this change of variables, the function factor is $f$ evaluated at the permuted input. The monomial transformation rule identifies the monomial on the original coordinates with the monomial on the permuted coordinate set (`monomial_permuteInput`). The inverse-image relation for the permuted set (`permuteFinset_symm`) then shows that the resulting expectation is precisely the Fourier coefficient of $f$ at the image of $S$ under $\pi^{-1}$.

**Key facts.** `FABL.monomial_permuteInput`, `FABL.permuteFinset_symm`.
