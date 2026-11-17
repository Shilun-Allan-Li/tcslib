<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.integrable_correlatedGaussianMeasure_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability under Correlated Gaussian Measure

**Claim.** If $f$ and $g$ belong to $L^2$ of the standard Gaussian product measure and $\rho\in[-1,1]$, then $(x,y)\mapsto f(x)g(y)$ is integrable under the correlated Gaussian measure.

**Proof.** The first marginal of the correlated measure is the standard Gaussian product measure, and so is the second marginal when $\rho\in[-1,1]$ (the marginal identities are `correlatedGaussianMeasure_fst` and `correlatedGaussianMeasure_snd`). Thus, composing $f$ and $g$ with the two coordinate projections preserves their respective $L^2$ membership. The product of two $L^2$ functions on a measure space is integrable by the Cauchy–Schwarz inequality. Applying this to those two compositions gives the result.

**Key facts.** `BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_fst`, `BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_snd`.
