<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: noiseKernel_nonneg -->
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

**Used in.** A granular positivity helper: it supplies the kernel-weight
nonnegativity side conditions in `corrExpect_mono`, in the induction step of the
two-function hypercontractivity theorem, and in the absolute-value bound for
`noiseOp` in the same file.
