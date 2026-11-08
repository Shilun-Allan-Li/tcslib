/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.PolyHierarchy.Padding
import TCSlib.Cryptography.Asymptotic.Adversary
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Helpers for collections: the index parameter, output lengths, coin split, padding

The machine-layer and string helpers of `TCSlib.Cryptography.Asymptotic.Collections`, which
imports this file: split off it, with every name unchanged, so that the collection interface has
room to grow under the 1000-line cap (gate 03b, finding 12 (b) and (d)). They are the
index-prepending machine of [PS10, Theorem 42.2 ⇐], the output-length bound of a machine and the
coin split of [PS10, Theorem 42.2 ⇒], the marker padding of the function `g` of that proof, and
the canonicity of the fixed-width decoder `decodeFin` (used by the collection instances for the
field `Collection.encD_decD`).

## Main definitions

* `Complexity.NUPPT.withIndexParam` — `B(1^n, y) = A(1^n, ⟨1^n, y⟩)` [PS10, Theorem 42.2 ⇐].
* `Complexity.NUPPT.runLenPoly` — a syntactic polynomial bounding `|A(1^n, y)|`.
* `TCSlib.Cryptography.splitCoins` — `{0,1}^{a+b} ≃ {0,1}^a × {0,1}^b`, the coins `(r₁, r₂)`
  of [PS10, Theorem 42.2 ⇒].

## Main results

* `Complexity.NUPPT.withIndexParam_runAt`, `Complexity.NUPPT.length_runAt_le`,
  `Complexity.NUPPT.length_runAt_le_runLenPoly` — the activation of `withIndexParam` and the
  output-length bounds.
* `TCSlib.Cryptography.ofFn_splitCoins_fst`, `ofFn_splitCoins_snd`, `ofFn_splitCoins_symm` —
  the coin split is `List.take`/`List.drop` on the encoded coin string.
* `TCSlib.Cryptography.Collection.ofFn_padFin_of_le`,
  `TCSlib.Cryptography.Collection.padFin_append_true_injective` — marker padding is lossless.
* `TCSlib.Cryptography.ofFn_of_decodeFin_eq_some` — `decodeFin` is canonical.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.5 Theorem 42.2.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The index parameter and output lengths of machines -/

/-- The machine `B(1^n, y) = A(1^n, ⟨1^n, y⟩)`: `A` with the unary parameter prepended to its
argument as the index of `FunFamily.toCollection`; same coins, same advice. -/
noncomputable def _root_.Complexity.NUPPT.withIndexParam (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (f := fun z => A.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (NUPPT.inParam z) (NUPPT.inArg z)) (NUPPT.inAdvice z) (NUPPT.inCoins z)))
    (A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam
      (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg)
      NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins))
    A.coins A.adv A.advice A.advice_length

/-- `withIndexParam` has the coins of `A`. -/
@[simp] theorem _root_.Complexity.NUPPT.coins_withIndexParam (A : NUPPT) :
    A.withIndexParam.coins = A.coins := by
  unfold NUPPT.withIndexParam
  exact NUPPT.coins_ofPolyTime _ _ _ _ _

/-- **`withIndexParam` runs on the coins of `A`**: the published equivalence
`A.withIndexParam.Coins n ≃ A.Coins n` (`NUPPT.coinsCongr` along `coins_withIndexParam`). -/
noncomputable def _root_.Complexity.NUPPT.withIndexParam_coinsEquiv (A : NUPPT) (n : ℕ) :
    A.withIndexParam.Coins n ≃ A.Coins n :=
  NUPPT.coinsCongr A.coins_withIndexParam n

/-- The coin equivalence keeps the coin string:
`List.ofFn (A.withIndexParam_coinsEquiv n r) = List.ofFn r`. -/
theorem _root_.Complexity.NUPPT.withIndexParam_coinsEquiv_ofFn (A : NUPPT) (n : ℕ)
    (r : A.withIndexParam.Coins n) : List.ofFn (A.withIndexParam_coinsEquiv n r) = List.ofFn r :=
  NUPPT.coinsCongr_ofFn A.coins_withIndexParam n r

/-- The activation of `withIndexParam`: `B(1^n, y; r) = A(1^n, ⟨1^n, y⟩; φ r)`, the coins read
through `φ = A.withIndexParam_coinsEquiv n`. -/
theorem _root_.Complexity.NUPPT.withIndexParam_runAt (A : NUPPT) (n : ℕ) (y : List Bool)
    (r : A.withIndexParam.Coins n) :
    A.withIndexParam.runAt n y r =
      A.runAt n (pairEncode (List.replicate n true) y) (A.withIndexParam_coinsEquiv n r) := by
  rw [NUPPT.runAt_eq, NUPPT.withIndexParam_coinsEquiv, NUPPT.runAt_coinsCongr]
  unfold NUPPT.withIndexParam
  rw [NUPPT.runAtL_ofPolyTime]
  simp only [NUPPT.runAtL_eq, NUPPT.layout_eq, NUPPT.inParam_eq, NUPPT.inArg_eq,
    NUPPT.inAdvice_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
    pairSndD_pairEncode]

/-- `|A(1^n, y; r)|` is bounded by the time bound at the length
`8n + 14 + 4|y| + 2·adv(n) + coins(n)` of the raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. -/
theorem _root_.Complexity.NUPPT.length_runAt_le (A : NUPPT) (n : ℕ) (y : List Bool)
    (r : A.Coins n) :
    (A.runAt n y r).length ≤
      A.Ct * (8 * n + 14 + 4 * y.length + 2 * A.adv.eval n + A.coins.eval n + 1) ^ A.ct := by
  refine (A.output_length_le _).trans ?_
  simp only [NUPPT.timeBound_def]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have := A.advice_length n
  simp only [length_pairEncode, NUPPT.length_advInput, List.length_ofFn, NUPPT.coinLen_eq]
  omega

/-- The syntactic polynomial bounding `|A(1^n, y)|` when `|y| ≤ Y(n)` (`length_runAt_le`). -/
def _root_.Complexity.NUPPT.runLenPoly (A : NUPPT) (Y : PolyExpr) : PolyExpr :=
  (PolyExpr.normal A.Ct A.ct).subst
    (.add (.add (.mul (.const 8) .var) (.const 14))
      (.add (.mul (.const 4) Y) (.add (.mul (.const 2) A.adv) A.coins)))

/-- Evaluation of `runLenPoly`. -/
theorem _root_.Complexity.NUPPT.eval_runLenPoly (A : NUPPT) (Y : PolyExpr) (n : ℕ) :
    (A.runLenPoly Y).eval n =
      A.Ct * (8 * n + 14 + 4 * Y.eval n + 2 * A.adv.eval n + A.coins.eval n + 1) ^ A.ct := by
  rw [NUPPT.runLenPoly, PolyExpr.eval_subst, PolyExpr.eval_normal]
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  ring

/-- `|A(1^n, y)| ≤ runLenPoly A Y (n)` whenever `|y| ≤ Y(n)`. -/
theorem _root_.Complexity.NUPPT.length_runAt_le_runLenPoly (A : NUPPT) {Y : PolyExpr} (n : ℕ)
    {y : List Bool} (hy : y.length ≤ Y.eval n) (r : A.Coins n) :
    (A.runAt n y r).length ≤ (A.runLenPoly Y).eval n := by
  rw [NUPPT.eval_runLenPoly]
  refine (A.length_runAt_le n y r).trans ?_
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  omega

/-! ## The coin split and marker padding of [PS10, Theorem 42.2 ⇒] -/

/-- A string of `a + b` bits as an `a`-bit and a `b`-bit string: the coins `(r₁, r₂)` of
[PS10, Theorem 42.2]. -/
def splitCoins (a b : ℕ) : (Fin (a + b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

/-- The first half of `splitCoins a b r` is the first `a` bits of the encoding of `r`. -/
theorem ofFn_splitCoins_fst (a b : ℕ) (r : Fin (a + b) → Bool) :
    List.ofFn (splitCoins a b r).1 = (List.ofFn r).take a := by
  refine List.ext_get ?_ fun i h₁ h₂ => ?_
  · simp
  · simp only [List.length_ofFn] at h₁
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn, List.getElem_take,
      List.getElem_ofFn]
    simp [splitCoins, Equiv.sumArrowEquivProdArrow_apply_fst, Equiv.sumArrowEquivProdArrow_apply_snd, Fin.coe_castAdd, Fin.coe_castLE]

/-- The second half of `splitCoins a b r` is the encoding of `r` after its first `a` bits. -/
theorem ofFn_splitCoins_snd (a b : ℕ) (r : Fin (a + b) → Bool) :
    List.ofFn (splitCoins a b r).2 = (List.ofFn r).drop a := by
  refine List.ext_get ?_ fun i h₁ h₂ => ?_
  · simp
  · simp only [List.length_ofFn] at h₁
    rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn, List.getElem_drop,
      List.getElem_ofFn]
    simp [splitCoins, Equiv.sumArrowEquivProdArrow_apply_fst, Equiv.sumArrowEquivProdArrow_apply_snd, Fin.coe_natAdd]

/-- The encoding of the coin string assembled from two halves is the concatenation of the
encodings of the halves. -/
theorem ofFn_splitCoins_symm (a b : ℕ) (r₁ : Fin a → Bool) (r₂ : Fin b → Bool) :
    List.ofFn ((splitCoins a b).symm (r₁, r₂)) = List.ofFn r₁ ++ List.ofFn r₂ := by
  set r := (splitCoins a b).symm (r₁, r₂) with hr
  have h1 : (splitCoins a b r).1 = r₁ := by rw [hr, Equiv.apply_symm_apply]
  have h2 : (splitCoins a b r).2 = r₂ := by rw [hr, Equiv.apply_symm_apply]
  rw [← h1, ← h2, ofFn_splitCoins_fst, ofFn_splitCoins_snd, List.take_append_drop]

namespace Collection

/-- The padding of a short string is the string followed by zeros. -/
theorem ofFn_padFin_of_le {ℓ : ℕ} {w : List Bool} (hw : w.length ≤ ℓ) :
    List.ofFn (padFin ℓ w) = w ++ List.replicate (ℓ - w.length) false := by
  refine List.ext_getElem (by simp; omega) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_ofFn, padFin_def, List.getD_eq_getElem?_getD]
  rw [List.getElem_append]
  split_ifs with h
  · rw [List.getElem?_eq_getElem h]
    rfl
  · rw [List.getElem?_eq_none (by omega)]
    simp

/-- **Marker padding is injective** on strings shorter than the padding length: the family
`owfFamily` loses no information about `⟨i, f_i(x)⟩`. -/
theorem padFin_append_true_injective {ℓ : ℕ} {s s' : List Bool} (hs : s.length < ℓ)
    (hs' : s'.length < ℓ) (h : padFin ℓ (s ++ [true]) = padFin ℓ (s' ++ [true])) : s = s' := by
  have h1 := congrArg List.ofFn h
  rw [ofFn_padFin_of_le (by simp; omega), ofFn_padFin_of_le (by simp; omega)] at h1
  have h2 := congrArg splitAtLastTrue h1
  simp only [List.append_assoc, List.singleton_append, PolyHierarchy.splitAtLastTrue_marker,
    Option.some.injEq] at h2
  exact h2

end Collection

/-! ## Canonicity of the fixed-width decoder -/

/-- **Decoding as an `ℓ`-bit string is canonical**: a string that `decodeFin ℓ` decodes to `x`
is `List.ofFn x` (the field `Collection.encD_decD` of the collections whose elements are
encoded by `List.ofFn`): the reversed-direction corollary of `decodeFin_eq_some_iff`. -/
theorem ofFn_of_decodeFin_eq_some {ℓ : ℕ} {w : List Bool} {x : Fin ℓ → Bool}
    (h : decodeFin ℓ w = some x) : List.ofFn x = w :=
  ((decodeFin_eq_some_iff ℓ w x).1 h).symm

end TCSlib.Cryptography
