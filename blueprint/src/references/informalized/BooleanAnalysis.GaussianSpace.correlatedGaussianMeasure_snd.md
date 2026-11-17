<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise.lean :: BooleanAnalysis.GaussianSpace.correlatedGaussianMeasure_snd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Marginal of the Correlated Gaussian Measure

**Claim.** For $\rho\in[-1,1]$, the second marginal of the correlated Gaussian measure is the standard Gaussian product measure $\gamma$.

**Proof.** Under the defining pushforward for the correlated measure, the second-coordinate projection is the map $(g,g')\mapsto \rho g+\sqrt{1-\rho^2}g'$. For $\rho\in[-1,1]$, this map preserves the product standard Gaussian measure and sends it to $\gamma$ ($\texttt{measurePreserving\_gaussianEndpoint}$). The pushforward-composition rule then identifies the second marginal with $\gamma$.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianEndpoint`.
