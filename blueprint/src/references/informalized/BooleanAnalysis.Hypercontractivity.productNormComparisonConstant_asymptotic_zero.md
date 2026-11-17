<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.productNormComparisonConstant_asymptotic_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison constant limit at zero

**Claim.** As $\lambda\to0$ through positive values, the comparison constant multiplied by $\sqrt\lambda$ tends to $1$.

**Proof.** The identity map tends to zero along the positive neighborhood of zero, and the standard logarithmic limit gives $\lambda\log\lambda\to0$. Continuity of $\log$ at $1$ then shows that $\log(1-\lambda)-2\lambda\log\lambda$ tends to zero, while $2(1-2\lambda)$ tends to $2$. Hence the quotient of these expressions tends to zero. Applying continuity of the exponential shows its exponential tends to $1$. For positive $\lambda$ sufficiently close to zero, in particular $0<\lambda<1/2$, the exceptional branch at $\lambda=1/2$ is absent. Taking logarithms of the defining real powers and using $\sqrt\lambda=\lambda^{1/2}$ shows that the product $C(\lambda)\sqrt\lambda$ equals the exponential of the quotient just considered. Therefore it tends to $1$.
