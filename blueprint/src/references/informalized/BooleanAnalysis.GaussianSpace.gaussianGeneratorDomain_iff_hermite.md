<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Generator.lean :: BooleanAnalysis.GaussianSpace.gaussianGeneratorDomain_iff_hermite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Generator Domain and Hermite Coefficients

**Claim.** For square-integrable $f$, membership in the Gaussian generator domain is equivalent to summability of the squared Hermite coefficients weighted by the square of the multi-index degree.

**Proof.** For the forward implication, take a generator $g$ witnessing that $f$ lies in the domain. The Hermite coefficient formula for a Gaussian generator says that the coefficient of $g$ at $\alpha$ is the degree $|\alpha|$ times the coefficient of $f$ (`hermiteCoeff_gaussianGenerator`). The squares of the Hermite coefficients of any square-integrable function are summable (`hermiteCoeff_sq_summable`); substituting the formula for $g$ gives the required weighted summability.

Conversely, assume the weighted sum is finite. Apply the Hermite coefficient realization result to the sequence $c_\alpha=|\alpha|\widehat f(\alpha)$: its squared summability is precisely the assumed condition. This produces a square-integrable function $g$ with those Hermite coefficients (`exists_memLp_hermiteCoeff`). The coefficient characterization of the Gaussian generator then gives that $g$ is a generator for $f` (`hasGaussianGenerator_of_hermiteCoeff`), so $f$ belongs to the domain.

**Key facts.** `BooleanAnalysis.GaussianSpace.hermiteCoeff_gaussianGenerator`, `BooleanAnalysis.GaussianSpace.hermiteCoeff_sq_summable`, `BooleanAnalysis.GaussianSpace.exists_memLp_hermiteCoeff`, `BooleanAnalysis.GaussianSpace.hasGaussianGenerator_of_hermiteCoeff`.
