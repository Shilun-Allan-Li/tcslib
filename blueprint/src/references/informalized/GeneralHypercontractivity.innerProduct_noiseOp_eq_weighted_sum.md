<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: innerProduct_noiseOp_eq_weighted_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Inner product with the noise operator as a kernel-weighted double sum

**Claim.** For any `ρ : ℝ` and `f g : BooleanFunc n`,

`innerProduct f (noiseOp ρ g)
   = uniformWeight n * ∑ x, ∑ y, noiseKernel ρ x y * f x * g y`,

i.e. `⟨f, T_ρ g⟩ = 2⁻ⁿ ∑_{x,y} K_ρ(x,y) f(x) g(y)`.

**Proof.**

1. `unfold innerProduct` and `simp [expect, Finset.mul_sum, mul_assoc]` turn the
   left side into `uniformWeight n * ∑ x, f x * noiseOp ρ g x`.
2. Rewrite the inner factor with `noiseOp_eq_kernel_sum`, replacing
   `noiseOp ρ g x` by `∑ y, noiseKernel ρ x y * g y` (`Finset.sum_congr` to work
   under the outer sum).
3. `simp [mul_comm, mul_left_comm, Finset.mul_sum]` pushes `f x` inside the
   `y`-sum and reassociates the three factors into the stated order.

**Used in.** The two-function hypercontractivity induction and the
`weighted_sum_succ_decomp` route in the same file: it is the bridge between the
operator-level statement `⟨f, T_ρ g⟩` and the kernel form that factors along
coordinates.
