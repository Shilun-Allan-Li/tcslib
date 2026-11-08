<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/GeneratingFunction.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_hermite_mul_exp_quadratic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Hermite exponential product

**Claim.** For each nonnegative integer $k$ and complex $x,z$, the function $w\mapsto H_k(x-w)\exp(xw-w^2/2)$ has derivative at $z$ equal to $H_{k+1}(x-z)\exp(xz-z^2/2)$.

**Proof.** Differentiate the exponent $xw-w^2/2$ at $z$; its derivative is $x-z$. The polynomial factor differentiates by the chain rule to $-H_k'(x-z)$. The product rule therefore gives the exponential times $(x-z)H_k(x-z)-H_k'(x-z)$. The Hermite recurrence identifies this expression with $H_{k+1}(x-z)$, proving the formula.
