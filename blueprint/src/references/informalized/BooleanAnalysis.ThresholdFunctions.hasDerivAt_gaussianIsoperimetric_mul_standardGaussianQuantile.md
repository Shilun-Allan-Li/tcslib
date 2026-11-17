<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.hasDerivAt_gaussianIsoperimetric_mul_standardGaussianQuantile -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of profile times quantile

**Claim.** At each $a\in(0,1)$, the function $p\mapsto U(p)Q(p)$ has derivative $1-Q(a)^2$.

**Proof.** Use the product rule with the profile derivative $U'(a)=-Q(a)$ (`hasDerivAt_gaussianIsoperimetric`) and the quantile derivative $Q'(a)=1/U(a)$ (`hasDerivAt_standardGaussianQuantile`). The resulting derivative is $-Q(a)^2+U(a)/U(a)$. The denominator is nonzero because the Gaussian density, and hence $U(a)$, is positive (`standardGaussianPDF_pos`). Simplifying gives $1-Q(a)^2$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.hasDerivAt_gaussianIsoperimetric`, `BooleanAnalysis.ThresholdFunctions.hasDerivAt_standardGaussianQuantile`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_pos`.
