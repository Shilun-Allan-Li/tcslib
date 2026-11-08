<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.anisotropicNoise_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Rates in Anisotropic Noise

**Claim.** When all coordinate rates in anisotropic noise equal $\rho$, its value at every outcome equals the product spectral noise with parameter $\rho$.

**Proof.** Expand anisotropic noise as a sum over coordinate subsets. For each subset $S$, the product of its coordinate rates is $\prod_{i\in S}\rho=\rho^{|S|}$. Thus each term agrees with the corresponding term in product spectral noise, and the sums are equal.
