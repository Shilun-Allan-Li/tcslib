/-- The polynomial-over-order correction is subexponentially small at every exponent below
one when the prime schedule is at least `2^κ`. This uses the shared subexponential notion.

**Proof sketch.** Bound the correction by `4d(κ)2⁻κ`, use the polynomial growth bound for
`d`, and apply `subexpSmall_two_pow_neg`, `SubexpSmall.mul_pow`, `.const_mul` and `.mono`. -/
theorem mddhSlack_subexpSmall (p : ℕ → ℕ) (d : PolyExpr)
    (hpb : ∀ κ, 2 ^ κ ≤ p κ) {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) :
    SubexpSmall c (mddhSlack p d) := by
  refine (TCSlib.Cryptography.CoinSampling.subexpSmall_polyExpr_mul
    subexpSmall_two_pow_neg zero_lt_one hc₁ ((PolyExpr.const 4).mul d)).mono ⟨0, ?_⟩
  intro κ _
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
    _ = (((PolyExpr.const 4).mul d).eval κ : ℝ) * (2 : ℝ)⁻¹ ^ κ := ?_
    _ ≤ |(((PolyExpr.const 4).mul d).eval κ : ℝ) * (2 : ℝ)⁻¹ ^ κ| := le_abs_self _
  simp only [PolyExpr.eval_mul, PolyExpr.eval_const, Nat.cast_mul, Nat.cast_ofNat]
  ring
