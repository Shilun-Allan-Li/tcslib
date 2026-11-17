<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.uniformLpNorm_two_noiseOperator_le_pow_of_degree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Bound from Fourier Degree

**Claim.** If $\rho\ge1$ and the Fourier degree of $f$ is at most $k$, then the uniform $L^2$ norm of the noise operator applied to $f$ is at most $\rho^k$ times the uniform $L^2$ norm of $f$.

**Proof.** Both sides of the desired inequality are nonnegative, so it suffices to compare their squares. The squared-norm identity in terms of the uniform inner product (`uniformLpNorm_two_sq_eq_uniformInner`), followed by Parseval's identity (`parseval`), turns the comparison into one between sums of squared Fourier coefficients. The noise operator multiplies the coefficient at a set $S$ by $\rho^{|S|}$ (`fourierCoeff_noiseOperator`). If $|S|\le k$, then $\rho^{|S|}\le\rho^k$ because $\rho\ge1$, so the corresponding squared coefficient is bounded by $\rho^{2k}$ times the original squared coefficient. If $|S|>k$, the degree hypothesis and `fourierDegree_le_iff` imply that the original coefficient vanishes, so this term contributes zero. Summing these termwise bounds gives the squared inequality; nonnegativity allows taking square roots and proves the claim.

**Key facts.** `FABL.uniformLpNorm_nonneg`, `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.parseval`, `FABL.fourierCoeff_noiseOperator`, `FABL.fourierDegree_le_iff`.
