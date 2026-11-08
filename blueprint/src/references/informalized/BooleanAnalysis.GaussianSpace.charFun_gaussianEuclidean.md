<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Linear.lean :: BooleanAnalysis.GaussianSpace.charFun_gaussianEuclidean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian vector characteristic function

**Claim.** For a vector $t\in\mathbb R^n$, the characteristic function of independent standard Gaussian coordinates is $\exp(-\|t\|^2/2)$.

**Proof.** The characteristic function of the product distribution factors into the product of the coordinate characteristic functions (`charFun_pi`). Each coordinate has the standard Gaussian characteristic function, so the product is the exponential of minus one half the sum of the squared coordinates. The Euclidean norm squared is precisely that sum, yielding $\exp(-\|t\|^2/2)$.
