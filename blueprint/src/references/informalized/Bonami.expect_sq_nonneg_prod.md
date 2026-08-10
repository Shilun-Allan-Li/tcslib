<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: expect_sq_nonneg_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Cross second moments are non-negative

**Claim.** For `g h : BooleanFunc n`, `0 ≤ expect (fun x => g x ^ 2 * h x ^ 2)`.

**Proof.** One line, the same shape as `expect_sq_nonneg`: after unfolding
`expect` the goal is `0 ≤ (2 : ℝ)⁻¹ ^ n * ∑ x, g x ^ 2 * h x ^ 2`, closed by
`mul_nonneg (pow_nonneg (by norm_num) _) (Finset.sum_nonneg fun _ _ => by positivity)`
— non-negative weight, and each summand is a product of squares. ∎

**Used in.** `bonami_expect` (`hC_nn`, the non-negativity of the cross term `C`
required by `bonami_algebra`) and `expect_fourth_nonneg`, which specialises it at
`h = 1`.
