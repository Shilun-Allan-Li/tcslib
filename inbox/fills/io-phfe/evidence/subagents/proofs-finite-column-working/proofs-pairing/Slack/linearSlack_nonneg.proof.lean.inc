/-- Averaging the nonnegative exact rank correction preserves nonnegativity.

**Proof sketch.** Apply the shared expectation monotonicity and constant expectation readers
to the pointwise nonnegative correction. -/
theorem linearSlack_nonneg (G : BilinearGen) (κ : ℕ) : 0 ≤ linearSlack G κ := by
  rw [linearSlack_eq]
  exact TCSlib.Cryptography.Games.ProbComp.expect_nonneg (publicParamsGen G κ)
    (fun pp => rankSlack_nonneg pp)
