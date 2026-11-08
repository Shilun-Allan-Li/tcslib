<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/UniformTransfer.lean :: BooleanAnalysis.GaussianSpace.continuous_gaussianPairTorusMap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of the Gaussian Pair Torus Map

**Claim.** For each natural number $n$, the map from pairs $(x,y)$ in $\mathbb R^n\times\mathbb R^n$ to the product torus indexed by the disjoint union of two copies of $\{1,\ldots,n\}\times\{0,1\}$, obtained by applying the Gaussian torus map to each vector, is continuous.

**Proof.** A map into a product space is continuous if each coordinate map is continuous. For a coordinate in the first copy, the map is the corresponding coordinate of the Gaussian torus map applied to $x$; it is continuous because projection onto $x$ is continuous and each coordinate of the Gaussian torus map is continuous. For a coordinate in the second copy, the same reasoning applies using projection onto $y$. Thus every coordinate is continuous, and so is the pair torus map.
