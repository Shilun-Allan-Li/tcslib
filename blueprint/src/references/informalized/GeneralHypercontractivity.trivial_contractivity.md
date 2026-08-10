<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: trivial_contractivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The noise operator is an Ls contraction for every s ≥ 1

**Claim.** For `s ≥ 1`, `0 ≤ ρ ≤ 1` and `f : BooleanFunc n`,
`(expect (fun x => |noiseOp ρ f x| ^ s)) ^ (1/s) ≤ (expect (fun x => |f x| ^ s)) ^ (1/s)`,
i.e. `‖T_ρ f‖_s ≤ ‖f‖_s`. No hypercontractive gain — just non-expansiveness.

**Proof.** Three steps.

1. Pointwise Jensen: `have h_ineq : ∀ x, |noiseOp ρ f x| ^ s ≤ ∑ y, noiseKernel ρ x y * |f y| ^ s`,
   which is `noiseOp_abs_rpow_le_kernel_avg hρ0 hρ1 s hs f x`.
2. Monotonicity of `t ↦ t ^ (1/s)` (`Real.rpow_le_rpow`) reduces the goal to the
   same inequality on the expectations; the uniform weight is pulled out with
   `mul_le_mul_of_nonneg_left` and `pow_nonneg`.
3. Sum step 1 over `x` (`Finset.sum_le_sum`), swap the order (`Finset.sum_comm`), and
   use that the kernel is stochastic in its first argument:
   `simp [← Finset.sum_mul, noiseKernel_sum_left hρ0 hρ1]` collapses
   `∑ x, noiseKernel ρ x y = 1`, leaving `∑ y, |f y| ^ s`. ∎

**Used in.** The `p = q` / degenerate branches of the general one-function
hypercontractivity theorems later in the file (4 call sites), where no gain is
available and mere contraction suffices.
