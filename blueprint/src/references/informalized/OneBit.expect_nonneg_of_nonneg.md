<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: expect_nonneg_of_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Expectation of a non-negative function is non-negative

**Claim.** For `f : BooleanFunc n` with `0 ≤ f x` for every `x`, we have
`0 ≤ expect f`.

**Proof.** One line. `unfold expect uniformWeight` makes the goal
`0 ≤ (2 : ℝ)⁻¹ ^ n * ∑ x, f x`, closed by
`mul_nonneg (pow_nonneg (by positivity) _) (Finset.sum_nonneg (fun x _ => hf x))`
— the uniform weight `2⁻ⁿ` is non-negative and the sum of non-negative terms is
non-negative. ∎

**Used in.** The positivity side goals of `holder_sharpness` (to know
`expect (fun x => |u x| ^ q)` is non-negative before dividing by a power of it),
and twice in `Hypercontractivity/General.lean` when discarding a factor bounded
by one via `mul_le_of_le_one_left`.
