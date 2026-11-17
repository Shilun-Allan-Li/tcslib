<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Basis.lean :: BooleanAnalysis.GaussianSpace.hermiteL2_dense -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Density of Hermite polynomials

**Claim.** For every dimension $n$, the linear span in $L^2(\mathbb R^n,\gamma_n)$ of the multivariate normalized Hermite functions is dense, where $\gamma_n$ is the product of $n$ standard Gaussian probability measures.

**Proof.** Fix an arbitrary element $f$ of the Gaussian $L^2$ space, and let $\varepsilon>0$. The density of polynomials in Gaussian $L^2$ (`gaussian_polynomial_dense`) provides a multivariate polynomial $P$ whose evaluation approximates $f$ within $\varepsilon$ in the $L^2$ norm. The class of this polynomial evaluation belongs to the span of the Hermite functions (`gaussianPolynomialLp_mem_span_hermiteL2`). Indeed, the Hermite polynomials span the polynomial space, and passing polynomial evaluation to its $L^2$ class preserves that linear combination. The distance in $L^2$ between $f$ and this class is the norm of their difference, hence the approximation estimate gives distance less than $\varepsilon$. Since this works for every positive $\varepsilon$, every $f$ lies in the closure of the Hermite span, proving density.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussian_polynomial_dense`, `BooleanAnalysis.GaussianSpace.gaussianPolynomialLp_mem_span_hermiteL2`, `BooleanAnalysis.GaussianSpace.memLp_eval_gaussian`.
