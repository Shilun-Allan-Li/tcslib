<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.variance_eq_hermite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Variance from Hermite coefficients

**Claim.** For $f\in L^2(\gamma_n)$, its variance is the sum of the squares of its normalized multivariate Hermite coefficients over all nonzero multi-indices.

**Proof.** Hermite Plancherel, applied with $f$ in both slots, expresses $\int f^2\,d\gamma_n$ as $\sum_\alpha c_\alpha^2$ (the integrability hypotheses hold because $f\in L^2$). The coefficient squares are summable, so this series can be split into the term at the zero multi-index and the sum over all other indices. The zero-index coefficient is the mean $\int f\,d\gamma_n$. The variance identity expresses variance as the second moment minus the square of the mean; substituting these two facts cancels the zero-index term and leaves precisely the sum over nonzero multi-indices.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermite_plancherel`, `BooleanAnalysis.GaussianSpace.hermiteCoeff_sq_summable`, `BooleanAnalysis.GaussianSpace.hermiteCoeff_zero`.
