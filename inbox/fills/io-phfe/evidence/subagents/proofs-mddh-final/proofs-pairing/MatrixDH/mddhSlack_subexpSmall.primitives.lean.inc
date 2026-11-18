/-- The polynomial-over-order correction is subexponentially small at every exponent below
one when the prime schedule is at least `2^κ`. This uses the shared subexponential notion.

**Proof sketch.** Bound the correction by `4d(κ)2⁻κ`, use the polynomial growth bound for
`d`, and apply `subexpSmall_two_pow_neg`, `SubexpSmall.mul_pow`, `.const_mul` and `.mono`. -/
theorem mddhSlack_subexpSmall (p : ℕ → ℕ) (d : PolyExpr)
    (hpb : ∀ κ, 2 ^ κ ≤ p κ) {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) :
    SubexpSmall c (mddhSlack p d) := by
  obtain ⟨C, k, hC⟩ := d.eval_le
  have he₀ : 0 < (c + 1) / 2 := ?_
  swap
  · linarith only [hc₀]
  have he₁ : (c + 1) / 2 < 1 := ?_
  swap
  · linarith only [hc₁]
  have hce : c < (c + 1) / 2 := ?_
  swap
  · linarith only [hc₁]
  have hbase := (subexpSmall_two_pow_neg.mul_pow zero_lt_one he₁ k).const_mul
    he₀ hce (4 * (C : ℝ) * 2 ^ k)
  refine hbase.mono ⟨1, ?_⟩
  intro κ hκ
  have hκ₁ : (1 : ℝ) ≤ κ := Nat.one_le_cast.mpr hκ
  have hd : (d.eval κ : ℝ) ≤ (C : ℝ) * ((κ : ℝ) + 1) ^ k := ?_
  swap
  · exact_mod_cast hC κ
  have hstep : (κ : ℝ) + 1 ≤ 2 * (κ : ℝ) := ?_
  swap
  · linarith only [hκ₁]
  have hpoly : (d.eval κ : ℝ) ≤ (C : ℝ) * 2 ^ k * (κ : ℝ) ^ k := ?_
  swap
  · calc
      _ ≤ (C : ℝ) * (2 * (κ : ℝ)) ^ k :=
        hd.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg _) zero_le_one) hstep k)
          (Nat.cast_nonneg _))
      _ = (C : ℝ) * 2 ^ k * (κ : ℝ) ^ k := ?_
    rw [_root_.mul_pow, mul_assoc]
  have hcast : (2 : ℝ) ^ κ ≤ (p κ : ℝ) := ?_
  swap
  · exact_mod_cast hpb κ
  have hdiv : (4 : ℝ) / (p κ : ℝ) ≤ 4 * (2 : ℝ)⁻¹ ^ κ := ?_
  swap
  · simpa only [div_eq_mul_inv, inv_pow] using
      (div_le_div_of_nonneg_left (a := (4 : ℝ)) zero_le_four
        (pow_pos two_pos κ) hcast)
  rw [mddhSlack_eq, abs_mul, Nat.abs_cast,
    abs_of_nonneg (div_nonneg zero_le_four (Nat.cast_nonneg _))]
  calc
    _ ≤ (d.eval κ : ℝ) * (4 * (2 : ℝ)⁻¹ ^ κ) :=
      mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)
    _ ≤ ((C : ℝ) * 2 ^ k * (κ : ℝ) ^ k) * (4 * (2 : ℝ)⁻¹ ^ κ) :=
      mul_le_mul_of_nonneg_right hpoly
        (mul_nonneg zero_le_four (pow_nonneg (inv_nonneg.mpr zero_le_two) κ))
    _ = (4 * (C : ℝ) * 2 ^ k) * ((κ : ℝ) ^ k * (2 : ℝ)⁻¹ ^ κ) := ?_
    _ ≤ |(4 * (C : ℝ) * 2 ^ k) * ((κ : ℝ) ^ k * (2 : ℝ)⁻¹ ^ κ)| := le_abs_self _
  ring
