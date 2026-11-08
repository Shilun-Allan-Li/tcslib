<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Polynomial.lean :: BooleanAnalysis.GaussianSpace.integral_gaussian_affine_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian affine monomial integral

**Claim.** For a product standard Gaussian vector $Y$, the expectation of $\prod_{i\in S}(a_i+sY_i)$ equals $\prod_{i\in S}a_i$.

**Proof.** For each coordinate define $g_i(y)=a_i+sy$ when $i\in S$, and $g_i(y)=1$ otherwise. Its one-dimensional Gaussian integral is $a_i$ in the first case: split the integral into its constant and linear parts, and use that a standard Gaussian has mean zero. In the second case its integral is $1$. The product inside the desired integral is $\prod_i g_i(Y_i)$. Independence of the standard Gaussian coordinates factors its integral into $\prod_i\int g_i\,d\gamma_1$ (`integral_fintype_prod_eq_prod`). Substituting the coordinate integrals gives $\prod_{i\in S}a_i$, since the other factors are $1$.
