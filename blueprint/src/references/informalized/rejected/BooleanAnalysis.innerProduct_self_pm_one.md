<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: innerProduct_self_pm_one -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.83) -->

# Unit norm of a ±1-valued function

**Claim.** If `f : BooleanFunc n` is `±1`-valued — `isPmOne f`, i.e.
`∀ x, f x = 1 ∨ f x = -1` — then `innerProduct f f = 1`.

**Proof.**

1. Unfold `innerProduct`, `expect`, `uniformWeight`: the goal is
   `(2 : ℝ)⁻¹ ^ n * ∑ x, f x * f x = 1`.
2. `have hsq : ∀ x, f x * f x = 1`, by `rcases hf x` on the two cases and
   `simp [h]` in each. Rewriting with `simp_rw [hsq]` makes the sum constant.
3. Evaluate the constant sum: `Finset.sum_const` and `Finset.card_univ` reduce
   it to `card (BoolCube n) • (1 : ℝ)`, and
   `Fintype.card_pi` + `Fintype.card_bool` + `Finset.prod_const` +
   `Finset.card_fin` compute that cardinality as `2 ^ n`.
4. `nsmul_eq_mul, mul_one` and `push_cast` leave `(2 : ℝ)⁻¹ ^ n * 2 ^ n = 1`,
   closed by `← mul_pow`, `inv_mul_cancel₀ (two_ne_zero)`, `one_pow`. ∎

**Used in.** `parseval_pm_one` (`∑_S f̂(S)² = 1` for `±1`-valued `f`, by
combining with `parseval`) and in `TCSlib/BooleanAnalysis/KKL.lean`.
