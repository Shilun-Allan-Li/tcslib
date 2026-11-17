<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_scalarGaussianEndpoint -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar Gaussian projection law

**Claim.** For $\rho\in[-1,1]$, the map $(x,y)\mapsto\rho x+\sqrt{1-\rho^2}\,y$ sends the product of two standard Gaussian measures to the standard Gaussian measure.

**Proof.** Choose $\theta=\arccos\rho$. The planar rotation by $\theta$ preserves the product Gaussian measure (rotation invariance, `measurePreserving_scalarGaussianRotation`). Projecting its output onto the first coordinate preserves the resulting standard Gaussian law, since the first-coordinate projection sends the product measure to the standard Gaussian measure. The first coordinate of the rotated pair is $\cos(\theta)x+\sin(\theta)y$. The angle identities give $\cos(\theta)=\rho$ and $\sin(\theta)=\sqrt{1-\rho^2}$, so this projection is exactly the stated map.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_scalarGaussianRotation`.
