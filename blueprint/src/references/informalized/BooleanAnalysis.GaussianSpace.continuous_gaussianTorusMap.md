<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Torus.lean :: BooleanAnalysis.GaussianSpace.continuous_gaussianTorusMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Gaussian Torus Map

**Claim.** For each natural number $n$, the map from $\mathbb R^n$ to the product torus indexed by $\{1,\ldots,n\}\times\{0,1\}$ sending $x$ to the coordinates represented by $x_i$ and $\sqrt{2}x_i$ modulo $1$ is continuous.

**Proof.** Continuity into a product follows from continuity of every coordinate. Fix an index $(i,b)$. If $b=0$, the coordinate is obtained by projecting to $x_i$ and then taking its class modulo $1$, a continuous map. If $b=1$, first multiply $x_i$ by the constant $\sqrt{2}$ and then take its class modulo $1$; both operations are continuous. Thus all coordinates, and therefore the torus map, are continuous.
