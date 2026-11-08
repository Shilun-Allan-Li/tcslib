<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_integral_gaussianPDFReal_meanDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second derivative of a bounded Gaussian average

**Claim.** For measurable $f$ with $|f(z)|\le1$, positive variance $v$, and real $c$, the derivative at $c$ of $m\mapsto\int ((z-m)/v)p_v(m,z)f(z)\,dz$ is $\int (((z-c)^2/v^2)-1/v)p_v(c,z)f(z)\,dz$.

**Proof.** Differentiate the integrand in $m$ using the derivative formula for the Gaussian mean score (`BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianPDFReal_meanDerivative`), then multiply by the fixed factor $f(z)$. To justify differentiating under the integral, take a neighborhood of $c$ where $|m|\le |c|+1$. The second mean derivative of the Gaussian density has an integrable bound uniform on this range (`BooleanAnalysis.GaussianSpace.gaussianPDFReal_secondMeanDerivative_dominated`), and $|f|\le1$ preserves it. The first mean derivative also has an integrable bound at $c$ (`BooleanAnalysis.GaussianSpace.gaussianPDFReal_meanDerivative_dominated`), ensuring integrability of the original integrand there. Measurability and the local uniform bound allow differentiation under the integral, yielding the stated integral of the pointwise derivative.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianPDFReal_secondMeanDerivative_dominated`, `BooleanAnalysis.GaussianSpace.gaussianPDFReal_meanDerivative_dominated`, `BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianPDFReal_meanDerivative`.
