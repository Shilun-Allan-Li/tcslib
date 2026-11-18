/-- Padded garbling draw coordinates fit the tape block. Technical size glue.

**Proof sketch.** For auxiliary coordinates use `PG.tCoord`, `auxCount_add_one` and
`mCount_le_mBound`; for output coordinates use the final-block offset and Fin.isLt. -/
theorem paddedDrawIndex_lt {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (κ : ℕ) (p : ℕ+) (f : Fn κ p)
    (u : PG.TIdx κ p f ⊕ Fin (n'.eval κ)) :
    paddedDrawIndex PG κ p f u < PG.mBound.eval κ + n'.eval κ := by
  rw [paddedDrawIndex_eq]
  cases u with
  | inl i =>
      simp only [Sum.elim_inl]
      have hi := (PG.tCoord κ p f i).isLt
      have hAux := PG.auxCount_add_one κ p f
      have hm := PG.mCount_le_mBound κ p f
      omega
  | inr j =>
      simp only [Sum.elim_inr]
      exact Nat.add_lt_add_left j.isLt (PG.mBound.eval κ)
