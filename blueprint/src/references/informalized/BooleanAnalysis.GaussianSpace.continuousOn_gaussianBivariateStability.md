<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Borell/Bivariate.lean :: BooleanAnalysis.GaussianSpace.continuousOn_gaussianBivariateStability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Continuity of Gaussian bivariate stability

**Claim.** For each correlation parameter $\rho\in[-1,1]$, Gaussian bivariate stability is continuous as a function of its two probability arguments on $[0,1]^2$.

**Proof.** The stated Lipschitz estimate bounds the change in bivariate stability between any two pairs of probability arguments in the square by twice the distance between those pairs. Every Lipschitz function on a set is continuous on that set, which gives the claim.

**Key facts.** `BooleanAnalysis.GaussianSpace.lipschitzOnWith_gaussianBivariateStability`.
