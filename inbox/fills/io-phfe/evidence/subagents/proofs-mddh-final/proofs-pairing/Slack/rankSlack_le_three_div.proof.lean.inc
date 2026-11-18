/-- The exact three-by-three rank correction is at most 3/p.
This coarse upper bound preserves the exact loss in the core inequality.

**Proof sketch.** For factors in [0,1], one minus their product is at most the sum of
one minus each factor. Bound 1/p² and 1/p³ by 1/p, using p≥2. -/
theorem rankSlack_le_three_div {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) :
    rankSlack pp ≤ 3 / (pp.group.order : ℝ) := by
  let q : ℝ := pp.group.order
  have hq : 1 ≤ q :=
    Nat.one_le_cast.mpr ((Nat.le_add_right 1 1).trans pp.group.order_prime.two_le)
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hx0 : (0 : ℝ) ≤ 1 / q := one_div_nonneg.mpr hq0
  have hy0 : (0 : ℝ) ≤ 1 / q ^ 2 := one_div_nonneg.mpr (pow_nonneg hq0 2)
  have hz0 : (0 : ℝ) ≤ 1 / q ^ 3 := one_div_nonneg.mpr (pow_nonneg hq0 3)
  have hx1 : (1 : ℝ) / q ≤ 1 := ?_
  swap
  · simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one hq
  have hyx : (1 : ℝ) / q ^ 2 ≤ 1 / q := ?_
  swap
  · simpa only [pow_one] using
      one_div_pow_le_one_div_pow_of_le hq (Nat.le_add_right 1 1)
  have hzx : (1 : ℝ) / q ^ 3 ≤ 1 / q := ?_
  swap
  · simpa only [pow_one] using
      one_div_pow_le_one_div_pow_of_le hq (Nat.le_add_right 1 2)
  have hz1 : (1 : ℝ) / q ^ 3 ≤ 1 := hzx.trans hx1
  have hrem : (0 : ℝ) ≤ (1 / q) * (1 / q ^ 2) * (1 - 1 / q ^ 3) +
      (1 / q) * (1 / q ^ 3) + (1 / q ^ 2) * (1 / q ^ 3) :=
    add_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg hx0 hy0) (sub_nonneg.mpr hz1))
        (mul_nonneg hx0 hz0))
      (mul_nonneg hy0 hz0)
  rw [rankSlack_eq]
  change 1 - (1 - 1 / q) * (1 - 1 / q ^ 2) * (1 - 1 / q ^ 3) ≤ 3 / q
  nlinarith only [hrem, hyx, hzx]
