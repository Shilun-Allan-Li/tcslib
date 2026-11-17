<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/GaussianTail.lean :: BooleanAnalysis.ThresholdFunctions.measurable_millsF' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of the Mills Integrand

**Claim.** The function $H(x)=\varphi(x)(1-3(x^4)^{-1})$, with the stated convention at zero, is measurable.

**Proof.** The standard Gaussian density $\varphi$ is continuous (`continuous_standardGaussianPDF`), hence measurable. The factor $x\mapsto1-3(x^4)^{-1}$ is measurable: it is built from the continuous power function, inversion, scalar multiplication, and subtraction, with inversion understood as the real-valued inverse that sends zero to zero. The product of measurable real-valued functions is measurable, so $H$ is measurable.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.continuous_standardGaussianPDF`.
