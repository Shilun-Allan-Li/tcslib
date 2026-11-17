<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_integral_gaussianPDFReal_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a bounded Gaussian average

**Claim.** For measurable $f$ with $|f(z)|\le1$, positive variance $v$, and real $c$, the derivative at $c$ of $m\mapsto\int p_v(m,z)f(z)\,dz$ is $\int ((z-c)/v)p_v(c,z)f(z)\,dz$.

**Proof.** To differentiate under the integral, restrict $m$ to a neighborhood of $c$ where $|m|\le |c|+1$. The Gaussian derivative admits an integrable bound uniform over means in this range (`BooleanAnalysis.GaussianSpace.gaussianPDFReal_meanDerivative_dominated`). Multiplication by $f$, whose absolute value is at most $1$, preserves that bound. The integrand is measurable, its derivative in $m$ is $((z-m)/v)p_v(m,z)f(z)$ by the Gaussian mean derivative formula (`BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianPDFReal_mean`), and the integrand at $m=c$ is integrable. The theorem for differentiating a parameterized integral under an integrable local derivative bound now gives the derivative as the integral of the pointwise derivative at $c$, as claimed.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianPDFReal_meanDerivative_dominated`, `BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianPDFReal_mean`.
