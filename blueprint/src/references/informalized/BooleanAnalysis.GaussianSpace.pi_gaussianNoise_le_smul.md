<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Density.lean :: BooleanAnalysis.GaussianSpace.pi_gaussianNoise_le_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Domination of a Gaussian product measure

**Claim.** Under the stated variance assumptions, the product of Gaussian laws with means $\rho x_i$ and variance $v$ is dominated by a finite constant times the product standard Gaussian measure.

**Proof.** For each coordinate $i$, let $K_i=\sqrt{2\pi}/\sqrt{2\pi v}\,\exp(x_i^2/2)$ and set $C$ equal to the product of the $K_i$ (regarded as a nonnegative extended real number). Each factor is nonnegative and finite, so $C$ is finite. By the Gaussian density bound (`gaussianPDFReal_noise_le`), the density in coordinate $i$ of the shifted, variance-$v$ Gaussian is at most $K_i$ times the standard Gaussian density. Multiplying these coordinatewise inequalities gives the corresponding bound on product densities; the product of the factors separates as $C$ times the product standard density. Both Gaussian product measures can be expressed as densities with respect to product Lebesgue measure (`pi_gaussianReal_eq_withDensity`). Comparing those densities pointwise therefore gives the asserted measure domination.

**Key facts.** `BooleanAnalysis.GaussianSpace.gaussianPDFReal_noise_le`, `BooleanAnalysis.GaussianSpace.pi_gaussianReal_eq_withDensity`.
