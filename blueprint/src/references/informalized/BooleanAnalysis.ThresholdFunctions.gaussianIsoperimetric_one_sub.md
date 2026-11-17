<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Profile.lean :: BooleanAnalysis.ThresholdFunctions.gaussianIsoperimetric_one_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetry of the Gaussian profile

**Claim.** For every $a\in(0,1)$, the Gaussian isoperimetric profile satisfies $U(1-a)=U(a)$.

**Proof.** The Gaussian quantile obeys $Q(1-a)=-Q(a)$ for $a\in(0,1)$ (`standardGaussianQuantile_one_sub`). Evaluating the profile at $1-a$ therefore evaluates the Gaussian density at $-Q(a)$. The standard Gaussian density is even, so this equals its value at $Q(a)$ (`standardGaussianPDF_neg`), which is $U(a)$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.standardGaussianQuantile_one_sub`, `BooleanAnalysis.ThresholdFunctions.standardGaussianPDF_neg`.
