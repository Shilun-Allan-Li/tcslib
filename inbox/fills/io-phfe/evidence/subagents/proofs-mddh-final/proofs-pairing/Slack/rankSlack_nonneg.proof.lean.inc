/-- The exact rank correction is nonnegative for every drawn prime-order group.

**Proof sketch.** Each factor of the invertible-matrix fraction lies between zero and one
because the prime order is at least two. Their product is at most one. -/
theorem rankSlack_nonneg {G : BilinearGen} {κ : ℕ} (pp : PublicParams G κ) :
    0 ≤ rankSlack pp := by
  have hq : (1 : ℝ) ≤ (pp.group.order : ℝ) :=
    Nat.one_le_cast.mpr ((Nat.le_add_right 1 1).trans pp.group.order_prime.two_le)
  have hq0 : (0 : ℝ) ≤ (pp.group.order : ℝ) := zero_le_one.trans hq
  have h2 : (1 : ℝ) / (pp.group.order : ℝ) ^ 2 ≤ 1 := ?_
  swap
  · simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one
      (one_le_pow₀ hq : (1 : ℝ) ≤ (pp.group.order : ℝ) ^ 2)
  have h3 : (1 : ℝ) / (pp.group.order : ℝ) ^ 3 ≤ 1 := ?_
  swap
  · simpa only [div_one] using one_div_le_one_div_of_le zero_lt_one
      (one_le_pow₀ hq : (1 : ℝ) ≤ (pp.group.order : ℝ) ^ 3)
  rw [rankSlack_eq]
  apply sub_nonneg.mpr
  exact mul_le_one₀
    (mul_le_one₀
      (sub_le_self _ (one_div_nonneg.mpr hq0))
      (sub_nonneg.mpr h2)
      (sub_le_self _ (one_div_nonneg.mpr (pow_nonneg hq0 2))))
    (sub_nonneg.mpr h3)
    (sub_le_self _ (one_div_nonneg.mpr (pow_nonneg hq0 3)))
