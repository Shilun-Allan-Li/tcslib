/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreGL

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Goldreich–Levin inverter for function families

The family side of [PS10, Theorem 87.3] (`FunFamily.StrongOneWay.glPad_hardCore` in
`Asymptotic/HardCore.lean`): the guess count `glK` for a predictor of advantage `n^{−c}` and its
polynomial majorant, the evaluator of the bit `⟨x, r⟩` on `⟨1^n, x ‖ r⟩`, the inverter
`glFamMachine` of `g(x, r) = (f(x), r)` obtained by wrapping the recovery machine `glMachine`
of `Asymptotic/HardCoreGL.lean` (applied to the predictor pre-processed to query `y ‖ q`), and
the identity `invProbOpt_glFam_eq` between its inversion probability and that of the concrete
inverter `HardcoreBit.guessInverter` [PS10, Algorithm 89.6; Gar26, Figure 2.5].

## Main definitions

* `TCSlib.Cryptography.glK`, `TCSlib.Cryptography.glKBound` — the guess count and its
  polynomial majorant.
* `TCSlib.Cryptography.glFamMachine` — the inverter of `g(x, r) = (f(x), r)`.

## Main results

* `TCSlib.Cryptography.glK_real`, `TCSlib.Cryptography.two_pow_glK_le` — the guess-count
  inequalities.
* `TCSlib.Cryptography.exists_glBitEvaluator` — the bit `⟨x, r⟩` is polynomial-time computable.
* `TCSlib.Cryptography.invProbOpt_glFam_eq` — the family inverter inverts exactly as often as
  `guessInverter`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.2–3.4.3: Theorem 87.3, Algorithm 89.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3, Figure 2.5).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The guess count and its bounds -/

/-- The guess count `k(n) := size (2 m(n) n^{2c})` of the reduction for a predictor of advantage
`n^{−c}`: `2 m n^{2c} < 2^k`, i.e. `2 m ≤ ε²(2^k − 1)` for `ε = n^{−c}`. -/
def glK (mP : PolyExpr) (c n : ℕ) : ℕ := Nat.size (2 * mP.eval n * n ^ (2 * c))

/-- The polynomial majorant `4 m n^{2c} + 1` of `2^{k(n)}`. -/
def glKBound (mP : PolyExpr) (c : ℕ) : PolyExpr :=
  .add (.mul (.const 4) (.mul mP (.pow .var (2 * c)))) (.const 1)

/-- `2 m n^{2c} < 2^{k(n)}`. -/
theorem lt_two_pow_glK (mP : PolyExpr) (c n : ℕ) : 2 * mP.eval n * n ^ (2 * c) < 2 ^ glK mP c n :=
  Nat.lt_size_self _

/-- `2^{k(n)} ≤ 4 m n^{2c} + 1`. -/
theorem two_pow_glK_le (mP : PolyExpr) (c : ℕ) (n : ℕ) :
    2 ^ glK mP c n ≤ (glKBound mP c).eval n := by
  simp only [glKBound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow,
    PolyExpr.eval_var]
  unfold glK
  calc 2 ^ Nat.size (2 * mP.eval n * n ^ (2 * c)) ≤ 2 * (2 * mP.eval n * n ^ (2 * c)) + 1 :=
        two_pow_size_le _
    _ = 4 * (mP.eval n * n ^ (2 * c)) + 1 := by ring

/-- The real form of the guess-count inequality: `2 m ≤ ε² (2^k − 1)` for `ε = 1/n^c`, `n ≥ 1`. -/
theorem glK_real (mP : PolyExpr) (c n : ℕ) (hn : 1 ≤ n) :
    2 * (mP.eval n : ℝ) ≤ (1 / (n : ℝ) ^ c) ^ 2 * ((2 : ℝ) ^ glK mP c n - 1) := by
  have h := lt_two_pow_glK mP c n
  have hnR : (0 : ℝ) < (n : ℝ) ^ c := pow_pos (by exact_mod_cast hn) c
  have hcast : (2 * (mP.eval n : ℝ) * (n : ℝ) ^ (2 * c)) + 1 ≤ (2 : ℝ) ^ glK mP c n := by
    exact_mod_cast h
  rw [one_div, inv_pow, ← pow_mul, mul_comm c 2]
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

/-- The guess count is positive when the block length is (`n ≥ 1`). -/
theorem glK_pos_or (mP : PolyExpr) (c n : ℕ) (hn : 1 ≤ n) :
    0 < 2 ^ glK mP c n - 1 ∨ mP.eval n = 0 := by
  rcases Nat.eq_zero_or_pos (mP.eval n) with hm | hm
  · exact Or.inr hm
  · left
    have h := lt_two_pow_glK mP c n
    have : 0 < 2 * mP.eval n * n ^ (2 * c) := by positivity
    omega

/-! ## The inverter of `g(x, r) = (f(x), r)` from the recovery machine -/

/-- Pre-processing of the family inverter: on the view of `⟨1^n, y ‖ r⟩`, the string
`y = (y ‖ r).take (outLen n)`. -/
def glFamPre (oP : PolyExpr) (v : List Bool) : List Bool :=
  (NUPPT.inArg v).take (oP.eval (NUPPT.inParam v).length)

/-- The pre-processing is polynomial-time. -/
theorem glFamPre_poly (oP : PolyExpr) : PolyTimeComputable (glFamPre oP) := by
  convert (polyTimeComputable_pairTakePoly oP).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg) using 1
  funext v
  simp [glFamPre]

/-- Post-processing of the family inverter: `answer ++ (y ‖ r).drop (outLen n)`. -/
def glFamPost (oP : PolyExpr) (v : List Bool) : List Bool :=
  pairSndD v ++ (NUPPT.inArg (pairFstD v)).drop (oP.eval (NUPPT.inParam (pairFstD v)).length)

/-- The post-processing is polynomial-time. -/
theorem glFamPost_poly (oP : PolyExpr) : PolyTimeComputable (glFamPost oP) := by
  have h : PolyTimeComputable fun v =>
      (NUPPT.inArg (pairFstD v)).drop (oP.eval (NUPPT.inParam (pairFstD v)).length) := by
    convert (polyTimeComputable_pairDropPoly oP).comp
      ((NUPPT.polyTimeComputable_inParam.comp polyTimeComputable_pairFstD).pairEncode
        (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairFstD)) using 1
    funext v
    simp
  exact polyTimeComputable_pairSndD.append h

/-- **The inverter of `g(x, r) = (f(x), r)`** [PS10, Algorithm 89.6]: the recovery machine on
`y = (y ‖ r).take (outLen n)`, its answer `x'` followed by `r`. -/
noncomputable def glFamMachine (A : NUPPT) (iP oP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) : NUPPT :=
  (glMachine A iP K k hk).wrap (glFamPre_poly oP) (glFamPost_poly oP) (fun _ => []) (.const 0)
    (fun _ => by simp) (.const 0)

/-- The family inverter on `y ‖ r` with coins `c` (as a string) returns the recovery machine's
answer on `y` followed by `r`. -/
theorem glFamMachine_runAt (A : NUPPT) (iP oP K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) (y : Fin (oP.eval n) → Bool) (r : Fin (iP.eval n) → Bool)
    (c : (glMachine A iP K k hk).Coins n) (r' : (glFamMachine A iP oP K k hk).Coins n)
    (hr' : List.ofFn r' = List.ofFn c) :
    (glFamMachine A iP oP K k hk).runAt n (List.ofFn y ++ List.ofFn r) r' =
      (glMachine A iP K k hk).runAt n (List.ofFn y) c ++ List.ofFn r := by
  unfold glFamMachine
  rw [NUPPT.runAt_wrap (glMachine A iP K k hk) (glFamPre_poly oP) (glFamPost_poly oP) _ _ _
    (.const 0) n _ rfl (fun _ : Fin 0 => false) c r' (by rw [hr']; rfl)]
  simp [glFamPre, glFamPost]

/-! ## The evaluator of `⟨x, r⟩` on `⟨1^n, x ‖ r⟩` -/

/-- **The evaluator of the Goldreich–Levin bit** `⟨x, r⟩` on `⟨1^n, x ‖ r⟩` (the efficiency clause
of [PS10, Theorem 87.3], Fact 88.4): cut after `inLen n` bits and apply `ipFun`. -/
theorem exists_glBitEvaluator (iP : PolyExpr) :
    ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
      ∀ n (x r : Fin (iP.eval n) → Bool),
        H (NUPPT.advInput n (List.ofFn x ++ List.ofFn r)) = [HardcoreBit.ip x r] := by
  refine ⟨fun w => ipFun (pairEncode ((pairSndD w).take (iP.eval (pairFstD w).length))
      ((pairSndD w).drop (iP.eval (pairFstD w).length))),
    ptcComp ipFun_poly ((polyTimeComputable_pairTakePoly iP).pairEncode
      (polyTimeComputable_pairDropPoly iP)), fun n x r => ?_⟩
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    take_ofFn_append, drop_ofFn_append, ipFun_ofFn]

/-! ## The inversion probability of the family inverter -/

/-- The pre-processing `⟨Y, q⟩ ↦ Y ++ q` of the family predictor. -/
def concatPre (z : List Bool) : List Bool := pairFstD z ++ pairSndD z

/-- The pre-processing is polynomial-time. -/
theorem concatPre_poly : PolyTimeComputable concatPre := polyTimeComputable_pairConcat

/-- The predictor of the family, called by the recovery machine on the pair `⟨y, q⟩`, computes
the concrete predictor `A(1^n, y ‖ q)` of [PS10, Algorithm 89.6]. -/
theorem glPredictorOf_precomp_concat (A : NUPPT) (n o m : ℕ) (y : Fin o → Bool) (q : Fin m → Bool)
    (c : A.Coins n) :
    glPredictorOf (A.precomp concatPre_poly) n m (fun y : Fin o → Bool => List.ofFn y) (y, q) c =
      A.predictor n (o + m) (Fin.appendEquiv o m (y, q)) c := by
  simp only [glPredictorOf, NUPPT.runAtL_precomp, concatPre, pairFstD_pairEncode, pairSndD_pairEncode,
    NUPPT.predictor, NUPPT.distinguisher, NUPPT.runAt_eq, ofFn_appendEquiv]


/-- **The inversion probability of the family inverter is that of the concrete inverter**
`guessInverter` of [PS10, Algorithm 89.6; Gar26, Figure 2.5] against `HardcoreBit.glPad (f n)`,
for the predictor `A'(y, q) = A(1^n, y ‖ q)`.

**Proof sketch.** Reindex the input by `appendEquiv` and the coins by `glCoinsEquiv` (the unread
coins are dropped by `uprob_fst`); on `(x, r)` with coins `(s, b, c)` the family inverter
returns `guessRecover … ‖ r` (`glFamMachine_runAt`, `glMachine_runAt_guessRecover`), which
inverts `g(x, r) = (f(x), r)` exactly when `guessInverter` does. -/
theorem invProbOpt_glFam_eq (𝓕 : FunFamily) (A : NUPPT) (K : PolyExpr) (k : ℕ → ℕ)
    (hk : ∀ n, 2 ^ k n ≤ K.eval n) (n : ℕ) (hM : 0 < 2 ^ k n - 1 ∨ 𝓕.inLen.eval n = 0) :
    invProbOpt (fun z : Fin (𝓕.inLen.eval n + 𝓕.inLen.eval n) → Bool =>
        Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)
          (HardcoreBit.glPad (𝓕.f n) ((Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n)).symm z)))
      ((glFamMachine (A.precomp concatPre_poly) 𝓕.inLen 𝓕.outLen K k hk).inverter n
        (𝓕.inLen.eval n + 𝓕.inLen.eval n) (𝓕.outLen.eval n + 𝓕.inLen.eval n)) =
    invProb (HardcoreBit.glPad (𝓕.f n))
      (HardcoreBit.guessInverter
        (fun y c => A.predictor n (𝓕.outLen.eval n + 𝓕.inLen.eval n)
          (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) c) (k n)) := by
  set A₁ := A.precomp concatPre_poly with hA₁
  have hpred : (fun (y : (Fin (𝓕.outLen.eval n) → Bool) × (Fin (𝓕.inLen.eval n) → Bool)) (c : A.Coins n) =>
      A.predictor n (𝓕.outLen.eval n + 𝓕.inLen.eval n) (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) y) c) =
      glPredictorOf A₁ n (𝓕.inLen.eval n) (fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y) := by
    funext y c
    obtain ⟨y, q⟩ := y
    exact (glPredictorOf_precomp_concat A n (𝓕.outLen.eval n) (𝓕.inLen.eval n) y q c).symm
  rw [hpred]
  unfold invProbOpt invProb
  have hcoins : (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).coinLen n = (glCoins 𝓕.inLen K A₁).eval n := by
    simp [glFamMachine, NUPPT.coinLen]
  let eC : HardcoreBit.GuessCoins (𝓕.inLen.eval n) (k n) (A₁.Coins n) ×
      (Fin ((glCoins 𝓕.inLen K A₁).eval n - glNeed A₁ 𝓕.inLen k n) → Bool) ≃
      (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).Coins n :=
    (glCoinsEquiv A₁ n (𝓕.inLen.eval n) (k n) _ (glNeed_le A₁ 𝓕.inLen K k hk n)).trans (finCastEquiv hcoins.symm)
  rw [← uprob_comp_equiv ((Equiv.prodAssoc ((Fin (𝓕.inLen.eval n) → Bool) × (Fin (𝓕.inLen.eval n) → Bool))
    (HardcoreBit.GuessCoins (𝓕.inLen.eval n) (k n) (A₁.Coins n))
    (Fin ((glCoins 𝓕.inLen K A₁).eval n - glNeed A₁ 𝓕.inLen k n) → Bool)).trans
    ((Fin.appendEquiv (α := Bool) (𝓕.inLen.eval n) (𝓕.inLen.eval n)).prodCongr eC))]
  refine (OneWay.uprob_congr fun w => ?_).trans (uprob_fst fun v : ((Fin (𝓕.inLen.eval n) → Bool) × (Fin (𝓕.inLen.eval n) → Bool)) ×
    HardcoreBit.GuessCoins (𝓕.inLen.eval n) (k n) (A₁.Coins n) =>
      HardcoreBit.glPad (𝓕.f n) (HardcoreBit.guessInverter
        (glPredictorOf A₁ n (𝓕.inLen.eval n) fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y) (k n)
        (HardcoreBit.glPad (𝓕.f n) v.1) v.2) = HardcoreBit.glPad (𝓕.f n) v.1)
  obtain ⟨⟨⟨x, r⟩, g⟩, ex⟩ := w
  simp only [Equiv.trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.symm_apply_apply, NUPPT.inverter_eq_some_iff]
  have hrun : (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).runAt n
      (List.ofFn (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n) (HardcoreBit.glPad (𝓕.f n) (x, r)))) (eC (g, ex)) =
      List.ofFn (HardcoreBit.guessRecover (glPredictorOf A₁ n (𝓕.inLen.eval n) (fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y))
        (k n) (𝓕.f n x) g) ++ List.ofFn r := by
    rw [ofFn_appendEquiv]
    show (glFamMachine A₁ 𝓕.inLen 𝓕.outLen K k hk).runAt n (List.ofFn (𝓕.f n x) ++ List.ofFn r) _ = _
    rw [glFamMachine_runAt A₁ 𝓕.inLen 𝓕.outLen K k hk n (𝓕.f n x) r
      (glCoinsEquiv A₁ n (𝓕.inLen.eval n) (k n) _ (glNeed_le A₁ 𝓕.inLen K k hk n) (g, ex)) _
      (by simp only [eC, Equiv.trans_apply]; exact ofFn_finCastEquiv _ _),
      glMachine_runAt_guessRecover A₁ 𝓕.inLen K k hk n hM (fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y)
        (𝓕.f n x) g ex]
  rw [hrun]
  constructor
  · rintro ⟨x', hx', hfx'⟩
    rw [← ofFn_appendEquiv, List.ofFn_inj] at hx'
    subst hx'
    rw [Equiv.symm_apply_apply] at hfx'
    exact (Fin.appendEquiv (𝓕.outLen.eval n) (𝓕.inLen.eval n)).injective hfx'
  · intro hinv
    refine ⟨Fin.appendEquiv (𝓕.inLen.eval n) (𝓕.inLen.eval n) (HardcoreBit.guessRecover
      (glPredictorOf A₁ n (𝓕.inLen.eval n) fun y : Fin (𝓕.outLen.eval n) → Bool => List.ofFn y) (k n) (𝓕.f n x) g, r),
      (ofFn_appendEquiv _ _).symm, ?_⟩
    rw [Equiv.symm_apply_apply]
    exact congrArg _ hinv

end TCSlib.Cryptography
