<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/General.lean :: BooleanAnalysis.Hypercontractivity.randomization_noise_eq_anisotropicNoise -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized product noise identity

**Claim.** Randomizing the product noise of \(f\) at rate \(c\) gives anisotropic noise whose coordinate rates are \(c\) times the signs determined by the random seed.

**Proof.** Evaluate both functions at an arbitrary outcome and expand their defining sums over subsets. The component of the product-noised function indexed by \(S\) is \(c^{|S|}\) times the corresponding component of \(f\) (\(\texttt{RandomizationAux.component\_noise}\)). Multiplying by the Walsh character contributes the product of the signs over \(S\). By multiplicativity of finite products, the resulting coefficient is \(\prod_{i\in S}(c\,\mathrm{boolToSign}(r_i))\), exactly the anisotropic-noise coefficient. The subset sums therefore agree at every outcome.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_noise`.
