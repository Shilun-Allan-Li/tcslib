<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Integration.lean :: BooleanAnalysis.GaussianSpace.integral_derivative_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian integration by parts

**Claim.** If $u$ and its derivative $u'$ are integrable under the standard Gaussian measure, and $x\mapsto xu(x)$ is integrable there, then the Gaussian integral of $u'$ equals the Gaussian integral of $xu$.

**Proof.** Multiply the derivative of $u$ by the standard Gaussian density and subtract the density times $xu$. This difference is the derivative of the product of the density and $u$: the density has derivative $-x$ times itself. The weighted integrability assumptions ensure both terms are integrable. The integral of this product derivative over the real line is zero, by the vanishing-at-infinity principle for an integrable derivative. Thus the two density-weighted integrals agree. Finally, converting Gaussian-density integrals back to integrals under the standard Gaussian measure gives the identity.

**Key facts.** `BooleanAnalysis.GaussianSpace.integrable_standardGaussianPDF_mul`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianPDF`.

**Caveat.** The supplied informal statement describes a different identity. This account follows the formal statement and proof source, which establish the one-dimensional Gaussian integration-by-parts formula.
