/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.ReductionSupport

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machines for PRG stretch extension

The evaluator iterates a string implementation of the one-bit generator and emits
one bit at each round. The reduction machine constructs the hybrid string from
its input and random coins, then calls the given distinguisher once
[PS10, Lemma 80.5].

## Main definitions

* `TCSlib.Cryptography.prgIterFun` is the iterated string evaluator.
* `TCSlib.Cryptography.expandRedPre` forms a hybrid string.
* `TCSlib.Cryptography.expandRedMachine` runs the distinguisher on that string.

## Main results

* `TCSlib.Cryptography.exists_expandEvaluator` gives a polynomial-time evaluator
  and its agreement with the typed expansion.
* `TCSlib.Cryptography.expandRedMachine_distinguisher` gives the hybrid machine's
  verdict on split coins.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.3.5, Lemma 80.5.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.3.1, Theorem 3.1.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Lemma 80.5: the iterated evaluation of a one-bit-stretch generator -/

/-- The seed update of the iterated evaluation: `w ↦ (F w).take |w|` (the first `|w|` bits of
the generator's output, the next seed `X_{i+1}` of [PS10, Lemma 80.5]). -/
def prgIterStep (F : List Bool → List Bool) (w : List Bool) : List Bool := (F w).take w.length

/-- The emitted bit of the iterated evaluation: `w ↦ (F w).drop |w|` (the last bit of the
generator's output, the bit `b_{i+1}` of [PS10, Lemma 80.5]). -/
def prgIterEmit (F : List Bool → List Bool) (w : List Bool) : List Bool := (F w).drop w.length

/-- The iterated evaluation: the output bits of `ℓ(|s|) + 1` rounds of the generator from the
seed `s`, concatenated (`Complexity.polyTimeComputable_iterateEmit`). -/
def prgIterFun (F : List Bool → List Bool) (ℓ : PolyExpr) (s : List Bool) : List Bool :=
  (List.range (ℓ.eval s.length + 1)).flatMap fun i => prgIterEmit F ((prgIterStep F)^[i] s)

/-- The seed update is polynomial-time (`polyTimeComputable_pairTakePoly var` on `⟨w, F w⟩`). -/
theorem prgIterStep_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (prgIterStep F) := by
  convert (polyTimeComputable_pairTakePoly .var).comp (polyTimeComputable_id.pairEncode hF) using 1
  funext w
  simp [prgIterStep]

/-- The emitted bit is polynomial-time (`polyTimeComputable_pairDropPoly var` on `⟨w, F w⟩`). -/
theorem prgIterEmit_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) :
    PolyTimeComputable (prgIterEmit F) := by
  convert (polyTimeComputable_pairDropPoly .var).comp (polyTimeComputable_id.pairEncode hF) using 1
  funext w
  simp [prgIterEmit]

/-- The seed update never lengthens a word, so its orbit stays within the input length. -/
theorem length_prgIterStep_iterate_le (F : List Bool → List Bool) (w : List Bool) (i : ℕ) :
    ((prgIterStep F)^[i] w).length ≤ w.length := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (List.length_take_le _ _).trans ih

/-- **The iterated evaluation is polynomial-time** (instance of
`Complexity.polyTimeComputable_iterateEmit` with `R := ℓ` and orbit bound `P := var`). -/
theorem prgIterFun_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) (ℓ : PolyExpr) :
    PolyTimeComputable (prgIterFun F ℓ) :=
  polyTimeComputable_iterateEmit (prgIterStep_poly hF) (prgIterEmit_poly hF) ℓ .var
    (fun x i _ => length_prgIterStep_iterate_le F x i)

section Generator

variable (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) {F : List Bool → List Bool}
  (hFs : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s))

include hFs

/-- On an encoded seed the seed update computes the first `n` bits of `G(s)`. -/
theorem prgIterStep_ofFn (n : ℕ) (s : Fin n → Bool) :
    prgIterStep F (List.ofFn s) = List.ofFn (Fin.init (G n s)) := by
  unfold prgIterStep
  rw [hFs, List.length_ofFn, ofFn_eq_init_append, List.take_left' List.length_ofFn]

/-- On an encoded seed the emitted bit is the last bit of `G(s)`. -/
theorem prgIterEmit_ofFn (n : ℕ) (s : Fin n → Bool) :
    prgIterEmit F (List.ofFn s) = [G n s (Fin.last n)] := by
  unfold prgIterEmit
  rw [hFs, List.length_ofFn, ofFn_eq_init_append, List.drop_left' List.length_ofFn]

/-- The iterates of the seed update on an encoded seed are the encoded iterates of
`s ↦ init (G s)`. -/
theorem prgIterStep_iterate_ofFn (n : ℕ) (s : Fin n → Bool) (i : ℕ) :
    (prgIterStep F)^[i] (List.ofFn s) = List.ofFn ((fun x => Fin.init (G n x))^[i] s) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, prgIterStep_ofFn G hFs, Function.iterate_succ_apply']

/-- **The iterated evaluation on an encoded seed** is the string of the `ℓ(n) + 1` output bits
`G(X_i)_{last}`, `X_i` the `i`-th iterate of `s ↦ init (G s)`. -/
theorem prgIterFun_ofFn (ℓ : PolyExpr) (n : ℕ) (s : Fin n → Bool) :
    prgIterFun F ℓ (List.ofFn s) =
      List.ofFn fun i : Fin (ℓ.eval n + 1) => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
  unfold prgIterFun
  rw [List.length_ofFn]
  refine List.ext_getElem (by simp [List.length_flatMap, prgIterStep_iterate_ofFn G hFs,
    prgIterEmit_ofFn G hFs]) fun j hj₁ hj₂ => ?_
  have hmap : ((List.range (ℓ.eval n + 1)).flatMap fun i =>
      prgIterEmit F ((prgIterStep F)^[i] (List.ofFn s))) =
      (List.range (ℓ.eval n + 1)).map fun i => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
    rw [List.map_eq_flatMap]
    congr 1
    funext i
    rw [prgIterStep_iterate_ofFn G hFs, prgIterEmit_ofFn G hFs]
  simp only [hmap, List.getElem_map, List.getElem_range, List.getElem_ofFn]

/-- The first `ℓ(n)` bits of the iterated evaluation: the output of the expansion `G'` of
[PS10, Lemma 80.5]. -/
theorem take_prgIterFun_ofFn (ℓ : PolyExpr) (n : ℕ) (s : Fin n → Bool) :
    (prgIterFun F ℓ (List.ofFn s)).take (ℓ.eval n) =
      List.ofFn fun i : Fin (ℓ.eval n) => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
  rw [prgIterFun_ofFn G hFs, List.ofFn_succ', List.concat_eq_append,
    List.take_left' List.length_ofFn]
  rfl

/-- **The evaluator of the expansion `G'`** [PS10, Lemma 80.5, "`G'` is efficiently
computable"]: `s ↦ (prgIterFun F ℓ s).take (ℓ |s|)` is polynomial-time and computes the
`ℓ(n)` output bits. -/
theorem exists_expandEvaluator (hF : PolyTimeComputable F) (ℓ : PolyExpr) :
    ∃ E : List Bool → List Bool, PolyTimeComputable E ∧ ∀ n (s : Fin n → Bool),
      E (List.ofFn s) =
        List.ofFn fun i : Fin (ℓ.eval n) => G n ((fun x => Fin.init (G n x))^[i] s) (Fin.last n) := by
  refine ⟨fun w => (prgIterFun F ℓ w).take (ℓ.eval w.length), ?_, fun n s => ?_⟩
  · convert (polyTimeComputable_pairTakePoly ℓ).comp
      (polyTimeComputable_id.pairEncode (prgIterFun_poly hF ℓ)) using 1
    funext w
    simp
  · dsimp only
    rw [List.length_ofFn, take_prgIterFun_ofFn G hFs]

end Generator

/-! ## Lemma 80.5: the hybrid distinguisher -/

/-- The pre-processing of the hybrid-`k` reduction of [PS10, Lemma 80.5] on the view
`⟨⟨⟨1^n, T⟩, c⟩, ⟨1^k, 1^{ℓ−k−1}⟩⟩`: the `ℓ`-bit string
`c.take k ++ T.drop n ++ (prgIterFun F ℓ (T.take n)).take (ℓ − k − 1)` — `k` uniform bits,
the given bit `T_{n+1}`, and `ℓ − k − 1` bits generated from the given seed `T_1 ⋯ T_n`. -/
def expandRedPre (F : List Bool → List Bool) (ℓ : PolyExpr) (w : List Bool) : List Bool :=
  (NUPPT.inAdvice w).take (pairFstD (NUPPT.inCoins w)).length ++
    (NUPPT.inArg w).drop (NUPPT.inParam w).length ++
    (prgIterFun F ℓ ((NUPPT.inArg w).take (NUPPT.inParam w).length)).take
      (pairSndD (NUPPT.inCoins w)).length

/-- The pre-processing of the hybrid reduction is polynomial-time. -/
theorem expandRedPre_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) (ℓ : PolyExpr) :
    PolyTimeComputable (expandRedPre F ℓ) :=
  ((takeLen_poly (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inCoins)
    NUPPT.polyTimeComputable_inAdvice).append
      (dropLen_poly NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg)).append
    (takeLen_poly (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inCoins)
      ((prgIterFun_poly hF ℓ).comp
        (takeLen_poly NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg)))

/-- **The hybrid-`k` distinguisher machine of [PS10, Lemma 80.5]** for a distinguisher `D` of
the expansion, a hybrid index family `k n < ℓ(n)` and the evaluator `F` of the generator:
advice `⟨⟨1^{k n}, 1^{ℓ(n) − k n − 1}⟩, D.advice n⟩`, coins `ℓ + D.coins`; on `⟨1^n, T⟩` it forms
the `ℓ(n)`-bit hybrid string (`expandRedPre`) and returns `D`'s verdict on it
(`Complexity.NUPPT.wrap`). -/
noncomputable def expandRedMachine (D : NUPPT) {F : List Bool → List Bool}
    (hF : PolyTimeComputable F) (ℓ : PolyExpr) (k : ℕ → ℕ) (hk : ∀ n, k n < ℓ.eval n) : NUPPT :=
  D.wrap (expandRedPre_poly hF ℓ) polyTimeComputable_pairSndD
    (fun n => pairEncode (List.replicate (k n) true) (List.replicate (ℓ.eval n - k n - 1) true))
    (.add (.mul (.const 3) ℓ) (.const 2)) (fun n => by
      rw [length_pairEncode, List.length_replicate, List.length_replicate]
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      have := hk n
      omega) ℓ

section Generator

variable (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) {F : List Bool → List Bool}
  (hFs : ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (G n s))

include hFs

/-- **The hybrid string** formed by `expandRedPre` on the view of `⟨1^n, T⟩` with data coins
`a` and advice `⟨1^k, 1^{ℓ−k−1}⟩` is the input of the concrete hybrid distinguisher
[Gar26, Theorem 3.1]: bit `i` is `a_i` for `i < k`, the given bit `T_{last}` at `i = k`, and
`G(X_{i−k−1})_{last}` beyond, with `X_j` the `j`-th iterate of `s ↦ init (G s)` on `init T`.

**Proof sketch.** Unfold the projections of the view; `T` splits as `init T ‖ [T_last]` (`ofFn_eq_init_append`) and the iterated evaluation is `prgIterFun_ofFn`; then `List.ext_getElem` with the three index ranges `i < k`, `i = k`, `i > k` (`List.getElem_append_left/right`, `List.getElem_take`, `List.getElem_ofFn`). -/
theorem expandRedPre_layout (ℓ : PolyExpr) (n k : ℕ) (hk : k < ℓ.eval n) (T : Fin (n + 1) → Bool)
    (a : Fin (ℓ.eval n) → Bool) :
    expandRedPre F ℓ (NUPPT.layout (List.replicate n true) (List.ofFn T) (List.ofFn a)
      (pairEncode (List.replicate k true) (List.replicate (ℓ.eval n - k - 1) true))) =
    List.ofFn fun i : Fin (ℓ.eval n) => if (i : ℕ) < k then a i else if (i : ℕ) = k then T (Fin.last n)
      else G n ((fun x => Fin.init (G n x))^[i - k - 1] (Fin.init T)) (Fin.last n) := by
  simp only [expandRedPre, NUPPT.inAdvice_layout, NUPPT.inCoins_layout, NUPPT.inArg_layout,
    NUPPT.inParam_layout, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
  rw [ofFn_eq_init_append T, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn,
    prgIterFun_ofFn G hFs]
  refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
  · simp only [List.length_append, List.length_take, List.length_ofFn, List.length_singleton]
    omega
  · simp only [List.length_ofFn] at hj₂
    simp only [List.getElem_ofFn]
    by_cases h1 : j < k
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_take, List.getElem_ofFn]
      simp [h1]
    · by_cases h2 : j = k
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp [h2]
      · rw [List.getElem_append_right (by simp; omega), List.getElem_take, List.getElem_ofFn]
        simp only [h1, h2, if_false, List.length_append, List.length_take, List.length_ofFn,
          List.length_singleton]
        rw [show j - (min k (ℓ.eval n) + 1) = j - k - 1 by omega]

/-- **The hybrid distinguisher machine computes the concrete hybrid reduction**: on coins
`r = a ++ c` its verdict on `T` is `D`'s verdict on the hybrid string with uniform bits `a`
and coins `c`. -/
theorem expandRedMachine_distinguisher (D : NUPPT) (hF : PolyTimeComputable F) (ℓ : PolyExpr)
    (k : ℕ → ℕ) (hk : ∀ n, k n < ℓ.eval n) (n : ℕ) (T : Fin (n + 1) → Bool)
    (a : Fin (ℓ.eval n) → Bool) (c : D.Coins n) (r : (expandRedMachine D hF ℓ k hk).Coins n)
    (hr : List.ofFn r = List.ofFn a ++ List.ofFn c) :
    (expandRedMachine D hF ℓ k hk).distinguisher n (n + 1) T r =
      D.distinguisher n (ℓ.eval n) (fun i => if (i : ℕ) < k n then a i
        else if (i : ℕ) = k n then T (Fin.last n)
        else G n ((fun x => Fin.init (G n x))^[i - k n - 1] (Fin.init T)) (Fin.last n)) c := by
  unfold expandRedMachine
  simp only [NUPPT.distinguisher_eq, NUPPT.distinguisherL_eq]
  rw [NUPPT.runAt_wrap D (expandRedPre_poly hF ℓ) polyTimeComputable_pairSndD _ _ _ ℓ n
    (List.ofFn T) rfl a c r hr, pairSndD_pairEncode, expandRedPre_layout G hFs ℓ n (k n) (hk n) T a]

end Generator

end TCSlib.Cryptography
