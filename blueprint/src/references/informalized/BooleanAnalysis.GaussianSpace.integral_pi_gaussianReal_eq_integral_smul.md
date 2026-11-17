<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/ProductDensity.lean :: BooleanAnalysis.GaussianSpace.integral_pi_gaussianReal_eq_integral_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Gaussian Density Formula

**Claim.** For a finite index type, the integral of a function under the product of Gaussian measures with coordinate means $c_i$ and common nonzero variance parameter $v$ equals its Lebesgue integral weighted by the product of the coordinate Gaussian densities.

**Proof.** The product Gaussian measure is the measure with density $z\mapsto\prod_i q_{c_i,v}(z_i)$ relative to product Lebesgue measure (`pi_gaussianReal_eq_withDensity`). Apply the integration formula for a measure defined by a density: integrate the function after multiplying it by that density. The density is nonnegative, so its extended-real value converts to the displayed real product without changing the integrand.

**Key facts.** `BooleanAnalysis.GaussianSpace.pi_gaussianReal_eq_withDensity`.
