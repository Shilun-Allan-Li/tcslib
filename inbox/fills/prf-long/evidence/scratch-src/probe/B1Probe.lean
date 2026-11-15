import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity

/-! prf-long fill, consumer-map probe: the clause (2) of the base's `SecureComputation.PRFOut` is
accepted as is by the delivered lemmas (the B1 steps 1 and 3 and the `spDecStr_wrongKey` budget).
Uses only the issue base and the delivered modules (nothing of #311/#312). -/

open Complexity Turing TCSlib.Cryptography

-- step 3 (total) at B1's hypothesis `hG : PRFOut ℓ G`, for any distinguisher `D'` and budget `q`
example {ℓ : PolyExpr} {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)}
    (hG : SecureComputation.PRFOut ℓ G) (D' : NUPPT) (q : PolyExpr) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (w w' : Fin (q.eval n + 1) → Fin (ℓ.eval n) → Bool),
      distAdv (fun z => encodeTupleOut (prfEncRealOut (G n) w z))
        (fun z => encodeTupleOut (prfEncRealOut (G n) w' z)) (D'.distinguisherL n) ≤ ε n :=
  MultiMsg.exists_negligible_distAdv_prfEncRealOut hG.pseudorandom D' q

-- step 1 (PRF step) at budget `q + 1`
example {ℓ : PolyExpr} {G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)}
    (hG : SecureComputation.PRFOut ℓ G) (B : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (G n) (B.toOracleAdversary n n (ℓ.eval n) ((q.add (.const 1)).eval n)) :=
  hG.pseudorandom.negligible_prfAdv B (q.add (.const 1))

-- `spDecStr_wrongKey`: `PRFOut (.add .var ℓ) G'`, one query
example (ℓ : PolyExpr)
    (G' : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin ((PolyExpr.add .var ℓ).eval n) → Bool))
    (hG' : SecureComputation.PRFOut (.add .var ℓ) G') (D : NUPPT) :
    ∃ B : NUPPT, (∀ n, ∃ φ : (Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin ((PolyExpr.add .var ℓ).eval n) → Bool)) (r : Fin n → Bool)
        (c : D.Coins n),
        (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1 (φ (r, c))).eval g =
          decide (D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) c = [true])) ∧
      Negligible fun n => prfAdv (G' n) (B.toOracleAdversary n n ((PolyExpr.add .var ℓ).eval n) 1) := by
  obtain ⟨B, hB⟩ := MultiMsg.exists_oneQuery_nuppt D (.add .var ℓ)
  exact ⟨B, hB, by simpa only [PolyExpr.eval_const] using hG'.pseudorandom.negligible_prfAdv B (.const 1)⟩
