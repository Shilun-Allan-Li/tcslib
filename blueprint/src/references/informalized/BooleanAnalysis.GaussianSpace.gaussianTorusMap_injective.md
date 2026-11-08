<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Torus.lean :: BooleanAnalysis.GaussianSpace.gaussianTorusMap_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Gaussian torus map

**Claim.** The map sending each real vector to its torus coordinates $x_i$ and $\sqrt2x_i$ is injective.

**Proof.** Suppose two vectors have the same image. Fix a coordinate $i$. Equality of their torus coordinates in the unscaled component implies that $x_i-y_i$ is an integer; equality in the scaled component implies that $\sqrt2(x_i-y_i)$ is an integer. If the first integer were nonzero, multiplying it by the irrational number $\sqrt2$ could not give an integer. Thus $x_i-y_i=0$. This holds for every coordinate, so the two vectors are equal.
