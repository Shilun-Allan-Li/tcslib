<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Marginal of the Correlated Gaussian Measure

**Claim.** The first marginal of the correlated Gaussian measure is the standard Gaussian product measure $\gamma$.

**Proof.** The correlated measure is the pushforward of $\gamma\times\gamma$ by the map sending $(g,g')$ to $(g,\rho g+\sqrt{1-\rho^2}g')$. Mapping this measure again by the first-coordinate projection is the same as pushing $\gamma\times\gamma$ forward by the composite map. That composite is simply $(g,g')\mapsto g$. Projection onto the first factor preserves the product measure, so the resulting measure is $\gamma$.
