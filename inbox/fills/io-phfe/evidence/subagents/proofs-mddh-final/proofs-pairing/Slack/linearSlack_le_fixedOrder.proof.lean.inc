/-- Every fixed prime schedule bounds the averaged correction by 3/p(κ).

**Proof sketch.** Use order_eq_of_publicParams to replace every drawn order by p(κ),
then average rankSlack_le_three_div and apply the constant expectation reader. -/
theorem linearSlack_le_fixedOrder (G : BilinearGen) (p : ℕ → ℕ)
    (hp : ∀ κ r, (G.inst κ r).order = p κ) (κ : ℕ) :
    linearSlack G κ ≤ 3 / (p κ : ℝ) := by
  rw [linearSlack_eq]
  calc
    _ ≤ TCSlib.Cryptography.Games.ProbComp.expect (publicParamsGen G κ)
        (fun _ => 3 / (p κ : ℝ)) :=
      TCSlib.Cryptography.Games.ProbComp.expect_mono (publicParamsGen G κ) ?_
    _ = 3 / (p κ : ℝ) :=
      TCSlib.Cryptography.Games.ProbComp.expect_const (publicParamsGen G κ) _
  intro pp
  simpa only [PublicParams.group_eq, order_eq_of_publicParams G p hp κ pp] using
    (rankSlack_le_three_div pp)
