<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.gaussianPDFReal_meanDerivative_dominated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Envelope for the first mean derivative

**Claim.** For positive variance $v$ and $M\ge0$, the absolute value of the first mean derivative of the Gaussian density is bounded uniformly over $|m|\le M$ by an integrable function of $z$.

**Proof.** Write $v$ for the positive real variance, and set $k=(\sqrt{2\pi v})^{-1}/v$ and $C=k\exp(M^2/(2v))$. Use the envelope $b(z)=C(|z|+M)\exp(-z^2/(4v))$. It is integrable because both the Gaussian exponential and its product with $|z|$ are integrable. If $|m|\le M$, then $|z-m|\le |z|+M$ and $m^2\le M^2$. The quadratic estimate $-2(z-m)^2\le 2M^2-z^2$ therefore bounds the shifted Gaussian exponential by $\exp(M^2/(2v))\exp(-z^2/(4v))$. Substituting the density formula and multiplying these bounds gives $|(z-m)p_v(m,z)/v|\le b(z)$ for every $z$.
