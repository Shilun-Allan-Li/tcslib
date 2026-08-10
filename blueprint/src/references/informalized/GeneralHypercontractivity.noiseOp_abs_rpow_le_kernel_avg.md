<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: noiseOp_abs_rpow_le_kernel_avg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Jensen's inequality for the noise kernel

**Claim.** For `0 ≤ ρ ≤ 1`, `s ≥ 1`, `f : BooleanFunc n` and `x : BoolCube n`,
`|noiseOp ρ f x| ^ s ≤ ∑ y : BoolCube n, noiseKernel ρ x y * |f y| ^ s`
(real `rpow` throughout). The `s`-th power of a kernel average is at most the
kernel average of the `s`-th powers.

**Proof.**

1. `h_triangle`: `|T_ρ f x| ≤ ∑ y K_ρ(x,y) · |f y|`. Rewrite by
   `noiseOp_eq_kernel_sum`, apply `Finset.abs_sum_le_sum_abs`, and on each term
   use `abs_mul` with `abs_of_nonneg (noiseKernel_nonneg hρ0 hρ1 x y)` to drop the
   absolute value on the (nonnegative) kernel.
2. `h_jensen`: `fun t => t ^ s` is convex on `Set.Ici 0`, by `convexOn_rpow`
   (needs `1 ≤ s`).
3. Monotonicity of `rpow` (`Real.rpow_le_rpow`) upgrades step 1 to
   `|T_ρ f x|^s ≤ (∑ y K_ρ(x,y) |f y|)^s`, and `ConvexOn.map_sum_le` then moves
   the power inside the sum. Its two side conditions are the kernel's
   nonnegativity (`noiseKernel_nonneg`) and that the weights sum to `1`
   (`noiseKernel_sum_right hρ0 hρ1 x`).

**Used in.** `trivial_contractivity` — the pointwise bound that, after averaging
over `x` and using `noiseKernel_sum_left`, gives the unconditional `L^s`
contractivity of `T_ρ`.
