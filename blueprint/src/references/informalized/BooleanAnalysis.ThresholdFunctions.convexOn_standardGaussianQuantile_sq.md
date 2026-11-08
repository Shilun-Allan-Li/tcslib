<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.convexOn_standardGaussianQuantile_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convexity of the squared Gaussian quantile

**Claim.** The function $p\mapsto Q(p)^2$ is convex on $(0,1)$.

**Proof.** Use the derivative criterion for convexity on an interval: it suffices to exhibit a first derivative that is continuous, a second derivative, and show that the second derivative is nonnegative. On $(0,1)$, continuity of $Q$ makes $Q^2$ continuous. The quantile derivative formula gives $Q'(p)=1/I(p)$, where $I$ denotes the Gaussian isoperimetric function (hasDerivAt_standardGaussianQuantile). Differentiating the square therefore gives the first derivative $2Q(p)/I(p)$. The derivative formula $I'(p)=-Q(p)$ (hasDerivAt_gaussianIsoperimetric), together with the quotient rule, then gives the second derivative $2(1+Q(p)^2)/I(p)^2$. The denominator is nonzero because $I(p)$ is the strictly positive Gaussian density at the quantile (standardGaussianPDF_pos); the numerator and denominator are positive. Thus the second derivative is nonnegative throughout the interval, proving convexity by the criterion.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.continuousAt_standardGaussianQuantile`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianQuantile`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_gaussianIsoperimetric`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
