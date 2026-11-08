<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/GaussianDisagreement.lean :: FABL.gaussianPDF_mul_polar -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian Density in Polar Coordinates

**Claim.** For all real r and θ, the product of the standard Gaussian densities at r cos θ and r sin θ equals the product of the densities at r and 0.

**Proof.** Write each density as (2π)^{-1/2} exp(-x²/2). Multiplying the two values on the left combines the normalizing factors and, by exp(a)exp(b)=exp(a+b), combines their exponents. The identity cos²θ+sin²θ=1 makes the sum of the two squared arguments equal to r². Thus the exponential factor becomes exp(-r²/2). On the right, the density at 0 contributes the same normalizing factor and exponential factor 1, so the products agree.
