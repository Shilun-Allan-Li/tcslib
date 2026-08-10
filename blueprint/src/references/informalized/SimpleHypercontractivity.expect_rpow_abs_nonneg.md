<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Simple.lean :: expect_rpow_abs_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Real-power L^p expectations are nonnegative

**Claim.** For any real exponent `p` and any `f : BooleanFunc n`,
`0 ≤ expect (fun x => |f x| ^ p)`. Note `^ p` is `Real.rpow`, so no sign
condition on `p` is needed — the base `|f x|` is already nonnegative.

**Proof.** `unfold expect uniformWeight`, leaving `2⁻¹ ^ n * ∑ x, |f x| ^ p`.
Then `mul_nonneg (pow_nonneg (by positivity) _)` for the weight, and
`Finset.sum_nonneg` plus `positivity` on each summand. ∎

**Used in.** The `E₂ = 0` branch and the Hölder step of
`hypercontractivity_p_2_general`, and in `Hypercontractivity/General.lean`
(`weak two-function hypercontractivity`, `one_function_iff_two_function_hypercontractivity`)
wherever `Real.rpow_le_rpow` or `Real.rpow_nonneg` needs the base to be
nonnegative. A deliberately granular side-condition helper.
