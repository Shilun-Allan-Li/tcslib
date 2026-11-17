<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.hermiteCoeff_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Order Hermite Coefficient

**Claim.** The Hermite coefficient of $f$ at the zero multi-index equals the Gaussian integral of $f$.

**Proof.** At the zero multi-index, each normalized one-variable Hermite polynomial is the constant polynomial $1$. Hence the multivariate Hermite function is identically $1$, and its coefficient integral $\int f(x)H_0(x)\,d\gamma(x)$ reduces to $\int f\,d\gamma$.
