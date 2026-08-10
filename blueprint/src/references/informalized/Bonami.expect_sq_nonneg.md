<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: expect_sq_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Second moments are non-negative

**Claim.** For `f : BooleanFunc n`, `0 ≤ expect (fun x => f x ^ 2)`.

**Proof.** One line. Unfolding `expect` makes the goal
`0 ≤ (2 : ℝ)⁻¹ ^ n * ∑ x, f x ^ 2`, closed by
`mul_nonneg (pow_nonneg (by norm_num) _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)`
— the weight `2⁻ⁿ` is non-negative and every summand is a square. ∎

**Used in.** Widely (16 call sites), including `bonami_expect` (`ha`, `hb`) and
the hypercontractivity development in `Hypercontractivity/Simple.lean`.
