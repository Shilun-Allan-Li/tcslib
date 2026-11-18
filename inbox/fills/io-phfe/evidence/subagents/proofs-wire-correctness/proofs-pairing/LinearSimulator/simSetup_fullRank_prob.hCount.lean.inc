by
    let q : ℕ := pp.group.order
    have hq₂ : 2 ≤ q := pp.group.order_prime.two_le
    have hq₁ : 1 ≤ q := (Nat.le_add_right 1 1).trans hq₂
    have h31 : 1 ≤ q ^ 3 := one_le_pow₀ hq₁
    have h3q : q ≤ q ^ 3 := le_self_pow₀ hq₁ (Nat.succ_ne_zero 2)
    have h32 : q ^ 2 ≤ q ^ 3 := pow_le_pow_right₀ hq₁ (Nat.le_succ 2)
    have hqne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr pp.group.order_prime.ne_zero
    have hcard : Fintype.card K = q := ZMod.card pp.group.order
    rw [hcard, Fin.prod_univ_three]
    change (((q ^ 3 - q ^ 0) * (q ^ 3 - q ^ 1) * (q ^ 3 - q ^ 2) : ℕ) : ℝ) /
        (q : ℝ) ^ 9 =
      (1 - 1 / (q : ℝ)) * (1 - 1 / (q : ℝ) ^ 2) *
        (1 - 1 / (q : ℝ) ^ 3)
    simp only [pow_zero, pow_one, Nat.cast_mul, Nat.cast_sub h31,
      Nat.cast_sub h3q, Nat.cast_sub h32, Nat.cast_pow, Nat.cast_one]
    field_simp [hqne] <;> ring
