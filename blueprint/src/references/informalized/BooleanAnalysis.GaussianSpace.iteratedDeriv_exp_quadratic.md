<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/GeneratingFunction.lean :: BooleanAnalysis.GaussianSpace.iteratedDeriv_exp_quadratic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the Hermite generating exponential

**Claim.** For every nonnegative integer $k$ and complex $x,z$, the $k$th derivative at $z$ of $w\mapsto\exp(xw-w^2/2)$ is $H_k(x-z)\exp(xz-z^2/2)$, where $H_k$ is the Hermite polynomial.

**Proof.** Proceed by induction on $k$, proving the identity for every evaluation point $z$. At order zero it is the defining expression, since the degree-zero Hermite polynomial is one. For the induction step, differentiate the order-$k$ expression as a function of its evaluation point. The derivative rule for a Hermite polynomial times this exponential says that its derivative is the same exponential multiplied by the next Hermite polynomial (\texttt{BooleanAnalysis.GaussianSpace.hasDerivAt_hermite_mul_exp_quadratic}). The recursive definition of iterated derivatives identifies this with the derivative of order $k+1$, proving the formula.

**Key facts.** `BooleanAnalysis.GaussianSpace.hasDerivAt_hermite_mul_exp_quadratic`.
