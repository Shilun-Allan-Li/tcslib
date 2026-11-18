/-- Exponential order growth makes the exact rank correction subexponentially small at
any positive exponent below one [JLS26, Section 1.1].

**Proof sketch.** Bound the nonnegative correction by 3·2⁻κ using the fixed-order bound.
Use subexpSmall_two_pow_neg and the shared constant-multiple and domination closures at
the requested smaller exponent. No negligible estimate is reproved locally. -/
theorem linearSlack_subexpSmall (G : BilinearGen) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ)
    {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) : SubexpSmall c (linearSlack G) := by
  refine (subexpSmall_two_pow_neg.const_mul zero_lt_one hc₁ 3).mono ⟨0, ?_⟩
  intro κ _
  have hcast : (2 : ℝ) ^ κ ≤ (p κ : ℝ) := ?_
  swap
  · exact_mod_cast hpb κ
  rw [abs_of_nonneg (linearSlack_nonneg G κ)]
  calc
    _ ≤ 3 / (p κ : ℝ) := linearSlack_le_fixedOrder G p hp κ
    _ ≤ 3 * (2 : ℝ)⁻¹ ^ κ := ?_
    _ ≤ |3 * (2 : ℝ)⁻¹ ^ κ| := le_abs_self _
  simpa only [div_eq_mul_inv, inv_pow] using
    (div_le_div_of_nonneg_left (a := (3 : ℝ)) zero_le_three
      (pow_pos two_pos κ) hcast)
