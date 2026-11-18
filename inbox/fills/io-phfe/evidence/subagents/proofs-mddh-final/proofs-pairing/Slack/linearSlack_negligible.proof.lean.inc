/-- Exponential order growth makes the exact rank correction negligible.

**Proof sketch.** Apply linearSlack_subexpSmall at exponent one half and the shared
SubexpSmall.negligible theorem. -/
theorem linearSlack_negligible (G : BilinearGen) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (hpb : ∀ κ, 2 ^ κ ≤ p κ) :
    Negligible (linearSlack G) := by
  exact (linearSlack_subexpSmall G p hp hpb (c := (1 : ℝ) / 2)
    (half_pos zero_lt_one) (half_lt_self zero_lt_one)).negligible (half_pos zero_lt_one)
