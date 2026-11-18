by
    intro κ
    have hp1 : (1 : ℝ) ≤ (p κ : ℝ) :=
      Nat.one_le_cast.mpr ((Nat.le_add_right 1 1).trans
        (orderSchedule_prime G p hp κ).two_le)
    have hp0 : (0 : ℝ) < (p κ : ℝ) := lt_of_lt_of_le zero_lt_one hp1
    have hx0 : 0 ≤ 1 / (p κ : ℝ) := one_div_nonneg.mpr hp0.le
    have hx1 : 1 / (p κ : ℝ) ≤ 1 := (div_le_one hp0).mpr hp1
    have h3 : (1 / (p κ : ℝ)) ^ 3 ≤ (1 / (p κ : ℝ)) ^ 2 :=
      pow_le_pow_of_le_one hx0 hx1 (Nat.le_succ 2)
    simp only [div_eq_mul_inv, one_mul, ← inv_pow] at hx0 h3 ⊢
    nlinarith only [hx0, h3, sq_nonneg ((p κ : ℝ)⁻¹)]
