<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianDensity.lean :: BooleanAnalysis.GaussianSpace.gaussianPDFReal_secondMeanDerivative_dominated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Envelope for the second mean derivative

**Claim.** For positive variance $v$ and $M\ge0$, the absolute value of the second mean derivative of the Gaussian density is bounded uniformly over $|m|\le M$ by an integrable function of $z$.

**Proof.** Set $k=(\sqrt{2\pi v})^{-1}$ and $C=k\exp(M^2/(2v))$. Take $b(z)=C\bigl(2(z^2+M^2)/v^2+1/v\bigr)\exp(-z^2/(4v))$. This is integrable, since it is a polynomial of degree two times a Gaussian exponential. For $|m|\le M$, one has $m^2\le M^2$, and expanding $(z-m)^2$ shows that the absolute value of $(z-m)^2/v^2-1/v$ is at most $2(z^2+M^2)/v^2+1/v$. As in the first-derivative envelope estimate, $-2(z-m)^2\le2M^2-z^2$ bounds the shifted density exponential by $\exp(M^2/(2v))\exp(-z^2/(4v))$. Combining the polynomial and exponential estimates with the density formula gives the claimed domination.
