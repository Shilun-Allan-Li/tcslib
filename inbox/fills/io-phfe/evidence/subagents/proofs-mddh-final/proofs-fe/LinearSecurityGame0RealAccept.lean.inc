/-- The two unfiltered padded real endpoint presentations coincide
[Wee20, Appendix B, Game 0, p. 12]. The substantive connection to the actual fresh raw
experiment is saGame_eq_freshSaGame in LinearSecurity.Endpoint.

**Proof sketch.** Read the two indexed game laws and their deterministic run readers.
For mode zero the optional middle-game filter is false, so both runs use exactly the
same public parameters, scalar tape, coin string and honest handler. -/
theorem game0_real_accept (G : BilinearGen) {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (zDim : PolyExpr) (A : SAAdv G PG zDim) (κ : ℕ) :
    accept (game G PG zDim A 0 κ) = accept (saGame G PG zDim A false κ) := by
  have hMode : decide (2 ≤ (0 : Fin 6).val) = false := rfl
  simp only [game_eq, saGame_eq, Bool.false_eq_true, if_false,
    runGameDet_eq, hMode, Bool.and_false, Bool.false_and]
