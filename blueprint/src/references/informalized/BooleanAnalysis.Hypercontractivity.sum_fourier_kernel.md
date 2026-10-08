<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean :: sum_fourier_kernel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The Fourier series of the noise kernel is a product

**Claim.** For `ρ : ℝ` and `x y : BoolCube n`,
`∑ S : Finset (Fin n), ρ ^ S.card * chiS S x * chiS S y = ∏ i, (1 + ρ * boolToSign (x i) * boolToSign (y i))`.
This is `2^n · noiseKernel ρ x y` written as a Fourier sum (the kernel itself
carries the extra `/2` per coordinate).

**Proof.** Two steps.

1. `have h_prod_sum`: expand the product over coordinates into a sum over subsets,
   `∏ i, (1 + t i) = ∑ S, ∏ i ∈ S, t i` with `t i = ρ * boolToSign (x i) * boolToSign (y i)`
   — `simp +decide [add_comm, Finset.prod_add]`.
2. Rewrite with it and compare summands termwise (`Finset.sum_congr rfl`): for each
   `S`, `∏ i ∈ S, (ρ * boolToSign (x i) * boolToSign (y i)) = ρ ^ |S| * chiS S x * chiS S y`
   by splitting the product over the three factors and unfolding the character
   — `simp_all +decide [Finset.prod_mul_distrib, chiS]`. ∎

**Used in.** `BooleanAnalysis.Hypercontractivity.noiseOp_eq_kernel_sum` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean`.
