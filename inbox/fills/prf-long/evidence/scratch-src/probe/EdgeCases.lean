import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF

/-! prf-long fill, edge-case probe (brief: *Check the edge cases*). Each `example` instantiates a
delivered statement at an edge of its parameters, through published names only; the file must
check with 0 errors. -/

open Complexity Turing TCSlib.Cryptography

-- ℓ(n) = 0: empty answers; a history block has `4n + 6` bits.
example (p : (Fin 5 → Bool) × (Fin 0 → Bool)) : (MultiMsg.histBlockOut p).length = 4 * 5 + 6 := by
  rw [MultiMsg.length_histBlockOut]

-- ℓ = const 0: the chain machine and the one-query machine exist (no side condition on ℓ).
example (D : NUPPT) (q : PolyExpr) (v : ∀ n, Fin (q.eval n + 1) → Fin ((PolyExpr.const 0).eval n) → Bool) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin (q.eval n + 1) → Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin ((PolyExpr.const 0).eval n) → Bool))
        (ρ : Fin (q.eval n + 1) → Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n ((PolyExpr.const 0).eval n) (q.eval n + 1) (φ (ρ, c))).eval g =
          decide (D.runAt n (List.ofFn fun j =>
            pairEncode (pairEncode (List.ofFn (ρ j)) (List.ofFn (v n j + g (ρ j)))) []).flatten c =
              [true]) :=
  MultiMsg.exists_queryChainOut_nuppt D q (.const 0) v

-- n = 0: the collision term is `C(q+1, 2) / 2^0 = C(q+1, 2)`.
example {q l : ℕ} {ρ : Type} [Fintype ρ] (m : Fin (q + 1) → Fin l → Bool)
    (D : (Fin (q + 1) → (Fin 0 → Bool) × (Fin l → Bool)) → ρ → Bool) :
    distAdv (prfEncRealOut (randomFunction (Fin 0 → Bool) (Fin l → Bool)) m) (otpEncOut m) D ≤
      (Nat.choose (q + 1) 2 : ℝ) := by
  simpa using distAdv_prfEncRealOut_random_otp_le (n := 0) m D

-- q = 0: one point, `C(1, 2) = 0`, so the inner switch is free.
example {n l : ℕ} {ρ : Type} [Fintype ρ] (m : Fin (0 + 1) → Fin l → Bool)
    (D : (Fin (0 + 1) → (Fin n → Bool) × (Fin l → Bool)) → ρ → Bool) :
    distAdv (prfEncRealOut (randomFunction (Fin n → Bool) (Fin l → Bool)) m) (otpEncOut m) D ≤ 0 := by
  simpa using distAdv_prfEncRealOut_random_otp_le (q := 0) m D

-- the one-query budget `1` (the statement of `exists_oneQuery_nuppt` uses the literal `1`).
example (D : NUPPT) (ℓ : PolyExpr) :
    ∃ B : NUPPT, ∀ n, ∃ φ : (Fin n → Bool) × D.Coins n ≃ B.Coins n,
      ∀ (g : (Fin n → Bool) → (Fin (ℓ.eval n) → Bool)) (r : Fin n → Bool) (c : D.Coins n),
        (B.toOracleAdversary n n (ℓ.eval n) 1 (φ (r, c))).eval g =
          decide (D.runAt n (pairEncode (List.ofFn r) (List.ofFn (g r))) c = [true]) :=
  MultiMsg.exists_oneQuery_nuppt D ℓ

-- the PRF-advantage bound at budget `const 1` reads as budget `1`.
example {ℓ₂ : PolyExpr} {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (ℓ₂.eval n) → Bool)}
    (hF : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := ℓ₂) F).Indist (OracleEnsemble.random .var ℓ₂))
    (B : NUPPT) : Negligible fun n => prfAdv (F n) (B.toOracleAdversary n n (ℓ₂.eval n) 1) := by
  simpa only [PolyExpr.eval_const] using hF.negligible_prfAdv B (.const 1)

-- block lengths are positive at every width: `0 < (histBlockLenOut ℓ).eval n`.
example (ℓ : PolyExpr) (n : ℕ) : 0 < (MultiMsg.histBlockLenOut ℓ).eval n := by
  rw [MultiMsg.eval_histBlockLenOut]; omega

-- the bridges at `l = n` / `ℓ = var`.
example {n q : ℕ} (v : Fin (q + 1) → (Fin n → Bool) × (Fin n → Bool)) :
    encodeTuple v = encodeTupleOut v := encodeTuple_eq_encodeTupleOut v
example (z : List Bool) : MultiMsg.postFun z = MultiMsg.postFunOut .var z :=
  MultiMsg.postFun_eq_postFunOut z
