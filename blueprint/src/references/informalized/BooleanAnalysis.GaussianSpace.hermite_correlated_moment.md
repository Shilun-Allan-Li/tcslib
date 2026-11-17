<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Noise.lean :: BooleanAnalysis.GaussianSpace.hermite_correlated_moment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlated Hermite moment

**Claim.** Let $\boldsymbol{\beta},\boldsymbol{\beta}'\in\mathbb N^n$ and $\rho\in[-1,1]$. For the stated jointly Gaussian vectors $(X,Y)$, the expectation of $H_{\boldsymbol{\beta}}(X)H_{\boldsymbol{\beta}'}(Y)$ is $\rho^{|\boldsymbol{\beta}|}$ when the indices agree and is $0$ otherwise.

**Proof.** First convert the expectation under the correlated Gaussian law into an integral under the standard product Gaussian law: for square-integrable functions $f,g$, the correlated-measure integration formula gives $\mathbb E[f(X)g(Y)]=\int f(x)\,\mathcal N_\rho g(x)\,d\gamma_n(x)$ (`integral_correlatedGaussianMeasure`). The Hermite functions are square integrable (`hermiteFunction_memLp_two`), so this formula applies. The Gaussian noise operator acts diagonally on each Hermite function: $\mathcal N_\rho H_{\boldsymbol{\beta}'}=\rho^{|\boldsymbol{\beta}'|}H_{\boldsymbol{\beta}'}$ (`gaussianNoise_hermiteFunction`). Pull this scalar outside the integral. The remaining integral is the inner product of the two Hermite functions, equal to $1$ for matching indices and $0$ otherwise (`integral_hermiteFunction_mul`). When the indices match, their coordinate sums agree, giving the stated power; when they do not, the integral vanishes.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_correlatedGaussianMeasure`, `BooleanAnalysis.GaussianSpace.hermiteFunction_memLp_two`, `BooleanAnalysis.GaussianSpace.gaussianNoise_hermiteFunction`, `BooleanAnalysis.GaussianSpace.integral_hermiteFunction_mul`.
