<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: noiseOp_eq_kernel_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The noise operator is a kernel sum

**Claim.** For every `ρ : ℝ`, `g : BooleanFunc n` and `x : BoolCube n`,
`noiseOp ρ g x = ∑ y : BoolCube n, noiseKernel ρ x y * g y`, where
`noiseKernel ρ x y = ∏ i, (1 + ρ * boolToSign (x i) * boolToSign (y i)) / 2`.
This converts the Fourier-side definition of `T_ρ`
(`∑_S ρ^{|S|} · fourierCoeff g S · chiS S x`) into an unnormalized sum against a
transition kernel — note the `1/2^n` of the uniform measure is absorbed into the
kernel, so no `uniformWeight` appears on the right.

**Proof.** Purely a computation on the two sums.

1. `unfold noiseOp noiseKernel fourierCoeff innerProduct`, then
   `simp [expect]` and `unfold uniformWeight` to expose both sides as sums over
   `BoolCube n` with an explicit `(1/2)^n` factor.
2. `simp [div_eq_inv_mul, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]`
   pushes the scalar and the `∑_S` inside.
3. `rw [Finset.sum_comm]` exchanges the sum over subsets `S` with the sum over
   points `y`, then `Finset.sum_congr rfl` works termwise (`ring_nf`).
4. `rw [← sum_fourier_kernel]` replaces the per-`y` inner sum
   `∑_S ρ^{|S|} · chiS S x · chiS S y` by the product
   `∏ i, (1 + ρ · sign(x i) · sign(y i))`; a final `simp` with the commutativity
   lemmas and `Finset.mul_sum` matches the two sides.

**Used in.** `innerProduct_noiseOp_eq_weighted_sum` (hence the whole
kernel-weighted route to `hypercontractivity_induction`) and
`noiseOp_abs_rpow_le_kernel_avg`.
