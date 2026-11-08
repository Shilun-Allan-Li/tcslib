<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/GaussianBobkov.lean :: BooleanAnalysis.GaussianSpace.integrable_gaussianGradient_of_bounded -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Bounded Gaussian Gradient Norm

**Claim.** If a continuous field of linear functionals on $\mathbb R^n$ has uniformly bounded operator norm, then the Euclidean norm of its coordinate values is integrable under the product standard Gaussian measure.

**Proof.** Apply `exists_boundedContinuous_bobkov_integrand` to the constant zero function and the given continuous field of linear functionals. It supplies a bounded continuous function equal at each point $x$ to the square root of the sum of the squared coordinate values, since the additional closed-profile term vanishes at zero (`closedGaussianProfile_zero`). Every bounded continuous function is integrable under the product standard Gaussian probability measure. The supplied pointwise identity therefore transfers integrability to the stated gradient norm.

**Key facts.** `BooleanAnalysis.GaussianSpace.exists_boundedContinuous_bobkov_integrand`, `BooleanAnalysis.GaussianSpace.closedGaussianProfile_zero`.
