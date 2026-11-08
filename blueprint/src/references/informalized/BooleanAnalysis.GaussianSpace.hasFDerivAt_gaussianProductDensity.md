<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDifferentiation.lean :: BooleanAnalysis.GaussianSpace.hasFDerivAt_gaussianProductDensity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a product Gaussian density

**Claim.** For a finite index set $I$, variance $v\geq0$, and $c,z\in\mathbb R^I$, the product Gaussian density as a function of its mean vector is differentiable at $c$. Its derivative is the linear functional $h\mapsto\sum_{i\in I}(\prod_{j\ne i}p_v(c_j,z_j))((z_i-c_i)/v)p_v(c_i,z_i)h_i$, with division by zero interpreted as zero.

**Proof.** For each coordinate $i$, the one-dimensional Gaussian density as a function of its mean has derivative $((z_i-c_i)/v)p_v(c_i,z_i)$ at $c_i$ (\texttt{hasDerivAt\_gaussianPDFReal\_mean}). Composing this function with the coordinate projection onto $i$ gives a derivative in direction $h$ equal to that coordinate derivative times $h_i$. The product rule for a finite product now sums these contributions, each multiplied by the density factors from all other coordinates. This is exactly the stated linear functional.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianPDFReal_mean`.
