<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Halfspace.lean :: BooleanAnalysis.GaussianSpace.standardGaussianCDF_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Standard Gaussian Distribution at Zero

**Claim.** The standard Gaussian distribution function satisfies $\Phi(0)=\frac12$.

**Proof.** Apply Sheppard's formula for the bivariate Gaussian quadrant probability at correlation $1$ (`BooleanAnalysis.ThresholdFunctions.sheppard_formula`). Since $\arccos(1)=0$, the probability that both coordinates are nonpositive is $1/2$. At correlation $1$, the quadrant event in this formula is represented by the event that the first coordinate is nonpositive. This event is $(-\infty,0]\times\mathbb R$, whose product measure is the standard Gaussian measure of $(-\infty,0]$ times the total mass of the second marginal. The latter mass is $1$, so the first factor is the Gaussian distribution function at zero. Hence $\Phi(0)=1/2$.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.sheppard_formula`.
