<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Linear.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_gaussianReflection -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian invariance under paired reflection

**Claim.** The map sending $(z,w)$ to the pair with coordinates $((\cos\theta)z_i+(\sin\theta)w_i)_i$ and $((\sin\theta)z_i-(\cos\theta)w_i)_i$ preserves the product standard Gaussian law.

**Proof.** Apply the planar rotation by $\theta$ to each pair of coordinates $(z_i,w_i)$. The paired rotation result (`measurePreserving_gaussianRotation`) preserves the product law. Then negate the second vector while leaving the first fixed; coordinatewise negation preserves the standard Gaussian product law (`measurePreserving_gaussianNeg`), as does the identity on the first factor, so their product map preserves the paired law. The composition has first output $(\cos\theta)z+(\sin\theta)w$ and second output $(\sin\theta)z-(\cos\theta)w$, by the rotation formula and elementary algebra. Hence the desired map preserves the law.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianRotation`, `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianNeg`.
