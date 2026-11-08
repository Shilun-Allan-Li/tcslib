<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications/LowDegree.lean :: BooleanAnalysis.Hypercontractivity.product_lowDegree_noise_norm_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Noise Second-Norm Bound

**Claim.** If c≥1 and f has no components indexed by sets larger than k, then the second norm of its noise transform at c is at most cᵏ times the second norm of f.

**Proof.** Parseval expresses the square of each second norm as the sum of the component energies. Under noise at c, the component indexed by S is multiplied by c^|S|. For |S|≤k, c^|S|≤cᵏ, so its squared coefficient is at most c^(2k); multiplying by the nonnegative component energy preserves this bound. For |S|>k the component vanishes by the degree assumption, so that term contributes zero. Summing gives ‖T_c f‖₂²≤c^(2k)‖f‖₂². Taking square roots and using cᵏ≥0 proves the result.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteProduct.parseval`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_noise`, `BooleanAnalysis.Hypercontractivity.FiniteProduct.expect_const_mul`.
