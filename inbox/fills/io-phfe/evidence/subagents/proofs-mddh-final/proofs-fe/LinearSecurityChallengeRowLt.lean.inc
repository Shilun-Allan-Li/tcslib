/-- Every accepted key's group-challenge row is in bounds, even when its function-dependent
node count is below the padded maximum. Technical size glue.

**Proof sketch.** Bound mCoord by mCount and then mBound. Combine j<q with the canonical
product-index bound. This also shows that no accepted query uses the identity default. -/
theorem challengeRow_lt {ℓ n' : PolyExpr} {Fn : ℕ → ℕ+ → Type}
    (PG : PartialGarbling.Raw ℓ n' Fn) (q : PolyExpr) (κ : ℕ) (p : ℕ+) (f : Fn κ p)
    (u : PG.MIdx κ p f) {j : ℕ} (hj : j < q.eval κ) :
    (PG.mCoord κ p f u).val * q.eval κ + j < (PG.mBound.mul q).eval κ := by
  rw [PolyExpr.eval_mul]
  have hm : (PG.mCoord κ p f u).val < PG.mBound.eval κ :=
    lt_of_lt_of_le (PG.mCoord κ p f u).isLt (PG.mCount_le_mBound κ p f)
  have hIndex := (finProdFinEquiv
    ((⟨(PG.mCoord κ p f u).val, hm⟩ : Fin (PG.mBound.eval κ)),
      (⟨j, hj⟩ : Fin (q.eval κ)))).isLt
  change j + q.eval κ * (PG.mCoord κ p f u).val <
    PG.mBound.eval κ * q.eval κ at hIndex
  simpa only [Nat.add_comm, Nat.mul_comm] using hIndex
