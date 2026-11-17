<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.hermite_expansion_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Hermite coefficients

**Claim.** If a Hermite series with coefficients $(c_\alpha)$ converges in $L^2(\gamma_n)$ to $f$, then each $c_\alpha$ equals the Hermite coefficient of $f$ at that index.

**Proof.** Fix a multi-index $\alpha$ and take the inner product of the convergent series with the Hermite function at $\alpha$. Continuity of the inner product carries the sum to the inner product of its limit with that function. Orthonormality of the Hermite functions makes the inner product of the $\beta$-term equal to $c_\beta$ when $\beta=\alpha$ and zero otherwise (`inner_hermiteL2`). The inner product of $f$ with the Hermite function at $\alpha$ is its defining integral coefficient (`inner_hermiteL2_toLp`). Hence the scalar series with only the $\alpha$-term nonzero has sum both $c_\alpha$ and that coefficient; uniqueness of limits gives their equality. Since $\alpha$ was arbitrary, the coefficient families agree.

**Key facts.** `BooleanAnalysis.GaussianSpace.inner_hermiteL2`, `BooleanAnalysis.GaussianSpace.inner_hermiteL2_toLp`.
