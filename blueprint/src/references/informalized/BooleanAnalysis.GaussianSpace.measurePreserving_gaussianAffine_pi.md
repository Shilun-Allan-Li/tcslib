<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDensity.lean :: BooleanAnalysis.GaussianSpace.measurePreserving_gaussianAffine_pi -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine Gaussian product law

**Claim.** The coordinatewise affine map sends the product of standard Gaussian measures to the product of Gaussian measures with means $c_i$ and variances $s^2$.

**Proof.** For each coordinate $i$, write $y\mapsto c_i+s y$ as the composition of scaling by $s$ and translation by $c_i$. Scaling a standard Gaussian by $s$ gives a centered Gaussian of variance $s^2$, and translating by $c_i$ gives mean $c_i$ while leaving that variance unchanged. Thus each coordinate map sends its standard Gaussian measure to the indicated Gaussian measure. Since the map acts independently coordinate by coordinate, the product measure preservation criterion gives the asserted product law.
