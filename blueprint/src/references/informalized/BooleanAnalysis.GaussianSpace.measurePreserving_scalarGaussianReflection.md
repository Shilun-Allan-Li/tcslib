<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_scalarGaussianReflection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian invariance under scalar reflection

**Claim.** For $\rho\in[-1,1]$, the map $(x,y)\mapsto(\rho x+\sqrt{1-\rho^2}\,y,\sqrt{1-\rho^2}\,x-\rho y)$ preserves the product of two standard Gaussian measures.

**Proof.** Set $\theta=\arccos\rho$. First apply the rotation by $\theta$, which preserves the product Gaussian measure by rotation invariance (`measurePreserving_scalarGaussianRotation`). Then leave the first coordinate unchanged and negate the second. Negation preserves the standard Gaussian measure, so this coordinatewise map also preserves the product measure. Composing these maps yields the stated transformation: the angle identities identify the coefficients, and simplifying the second coordinate gives $\sin(\theta)x-\cos(\theta)y$.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_scalarGaussianRotation`.
