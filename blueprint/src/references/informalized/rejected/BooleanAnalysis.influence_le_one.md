<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: influence_le_one -->
<!-- origin: boolean-ch02-social-choice-arrow run 352ab7ff3113 verdict not_in_text (0.82) -->

# Single-coordinate influence is at most one

**Claim.** Let `f : BooleanFunc n` be `±1`-valued (`hf : ∀ x, f x ∈ ({-1, 1} : Set ℝ)`)
and let `i : Fin n`. Then `influence i f ≤ 1`, where
`influence i f = expect (fun x ↦ (f x - f (flipBit x i))^2 / 4)`.

**Proof.** Unfold `influence`, `expect`, `uniformWeight`, so the goal is
`(2:ℝ)⁻¹^n * ∑ x, (f x - f (flipBit x i))^2 / 4 ≤ 1`.

1. `hcard`: the cube has `2^n` points — `Finset.card_univ`, `Fintype.card_pi`,
   `Fintype.card_bool`, `Finset.prod_const`, `Fintype.card_fin`.
2. `hsum`: each summand is at most `1`. Both `f x` and `f (flipBit x i)` lie in
   `{-1, 1}`, so the four sign cases (`rcases … <;> rw [h1, h2] <;> norm_num`)
   give `(f x - f (flipBit x i))^2 / 4 ∈ {0, 1}`. Summing termwise
   (`Finset.sum_le_sum`) and using step 1 bounds the sum by `2^n`.
3. Multiply by the nonnegative weight `(2:ℝ)⁻¹^n`
   (`mul_le_mul_of_nonneg_left`, `pow_nonneg`), then
   `(2:ℝ)⁻¹^n * 2^n = 1` by `← mul_pow` and `norm_num`. ∎

**Remark.** Only the `±1` hypothesis is used, via the fact that the squared
difference of two signs is `0` or `4`; nothing about `f` beyond its range enters.
