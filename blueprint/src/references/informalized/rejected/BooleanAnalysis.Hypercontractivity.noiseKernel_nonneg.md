<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean :: noiseKernel_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The noise kernel is nonnegative

**Claim.** For `0 ≤ ρ ≤ 1` and any `x y : BoolCube n`, the noise kernel
`noiseKernel ρ x y = ∏ i, (1 + ρ * boolToSign (x i) * boolToSign (y i)) / 2`
is nonnegative.

**Proof.**

1. `Finset.prod_nonneg` reduces the goal to nonnegativity of each factor
   `(1 + ρ * boolToSign (x i) * boolToSign (y i)) / 2`.
2. `cases x i <;> cases y i` splits into the four sign patterns; with
   `norm_num [boolToSign]` each factor becomes `(1 + ρ)/2` or `(1 - ρ)/2`,
   and `nlinarith` closes both from `0 ≤ ρ ≤ 1`.

**Used in.** `BooleanAnalysis.Hypercontractivity.noiseOp_abs_rpow_le_kernel_avg` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Duality.lean`; `BooleanAnalysis.Hypercontractivity.corrExpect_mono` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean`; `BooleanAnalysis.Hypercontractivity.two_func_hyp_succ` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Tensorization.lean`; `BooleanAnalysis.Hypercontractivity.noiseOp_nonneg` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean`; `BooleanAnalysis.Hypercontractivity.lpMean_noise_antitone` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Tensorization.lean`.
