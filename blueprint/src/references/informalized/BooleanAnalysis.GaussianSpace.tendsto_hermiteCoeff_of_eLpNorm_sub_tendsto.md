<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.tendsto_hermiteCoeff_of_eLpNorm_sub_tendsto -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of Hermite coefficients

**Claim.** If the functions $u_i$ converge to a square-integrable function $f$ in $L^2(\gamma_n)$ along a filter, then for every multi-index $\alpha$ their Gaussian Hermite coefficients converge to the coefficient of $f$, provided the $u_i$ are square-integrable eventually.

**Proof.** The difference of the two coefficients is the coefficient of $u_i-f$, by linearity of the Hermite coefficient for square-integrable functions (hermiteCoeff_sub). The coefficient bound (abs_hermiteCoeff_le_eLpNorm_toReal) bounds its absolute value by the real-valued $L^2$ norm of $u_i-f$. This upper bound tends to zero: apply continuity of the real-valued map $t\mapsto t$ on nonnegative extended reals at zero to the assumed convergence of the extended $L^2$ norms. Since the coefficient difference is bounded in absolute value by a quantity tending to zero, it too tends to zero, proving convergence of the coefficients.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteCoeff_sub`, `BooleanAnalysis.GaussianSpace.abs_hermiteCoeff_le_eLpNorm_toReal`.
